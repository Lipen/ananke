//! # Tic-Tac-Toe — Game Solving with Attractor Computation
//!
//! This example demonstrates BDD-based symbolic game solving using attractor
//! computation. We analyze the classic Tic-Tac-Toe (Noughts and Crosses) game
//! to determine winning/drawing/losing positions for each player.
//!
//! ## The Problem
//!
//! Tic-Tac-Toe is a two-player game on a 3×3 grid:
//! - Player X moves first
//! - Players alternate placing their mark in empty cells
//! - First to get 3-in-a-row (horizontal, vertical, diagonal) wins
//! - If the board fills with no winner, it's a draw
//!
//! ```text
//!        Initial          Example Game         X Wins!
//!       ─────────────     ─────────────     ─────────────
//!       │   │   │   │     │ X │   │ O │     │ X │ O │ O │
//!       ─────────────     ─────────────     ─────────────
//!       │   │   │   │  →  │ O │ X │   │  →  │ O │ X │ X │
//!       ─────────────     ─────────────     ─────────────
//!       │   │   │   │     │   │   │ X │     │ X │   │ X │
//!       ─────────────     ─────────────     ─────────────
//! ```
//!
//! ## Game Theory Background
//!
//! In game theory, we classify positions based on who can force a win:
//!
//! - **Winning position**: Current player can guarantee a win
//! - **Losing position**: Opponent can force a win no matter what we do
//! - **Drawing position**: Neither player can force a win; best play leads to draw
//!
//! ## Attractor Computation
//!
//! An **attractor** for player P towards goal G is the set of positions from
//! which P can force reaching G:
//!
//! ```text
//! Attr_P(G) = μZ. G ∨ (P_moves ∧ ∃ move to Z) ∨ (Opp_moves ∧ ∀ moves lead to Z)
//! ```
//!
//! In CTL terms:
//! - For maximizing player: similar to EF (can reach)
//! - For minimizing player: similar to AF (must reach)
//!
//! ## What We Compute
//!
//! 1. **X-winning positions**: Where X can force a win
//! 2. **O-winning positions**: Where O can force a win
//! 3. **Drawing positions**: Where best play leads to draw
//! 4. **Optimal play analysis**: Is the initial position a draw?
//!
//! ## State Encoding
//!
//! Each cell has 3 states (empty/X/O), encoded with 2 bits:
//! - 00 = Empty
//! - 01 = X
//! - 10 = O
//! - 11 = Invalid
//!
//! Plus 1 bit for whose turn: 0=X's turn, 1=O's turn
//! Total: 9 cells × 2 bits + 1 turn bit = 19 boolean variables
//!
//! Run with: `cargo run --example tictactoe --release`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use model_checking::{TransitionSystem, Var};

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

/// Cell values (encoded as 2-bit)
const EMPTY: u8 = 0b00;
const X_MARK: u8 = 0b01;
const O_MARK: u8 = 0b10;

/// Represents the Tic-Tac-Toe game model
struct TicTacToeModel {
    bdd: Rc<Bdd>,
    ts: TransitionSystem,
    /// Cell bits: cell_bits[i] = (lo, hi) for cell i (0-8)
    cell_bits: Vec<(Ref, Ref)>,
    cell_bits_next: Vec<(Ref, Ref)>,
    /// Turn bit: false = X's turn, true = O's turn
    turn: Ref,
    turn_next: Ref,
}

impl TicTacToeModel {
    fn new() -> Self {
        let bdd = Rc::new(Bdd::default());
        let mut ts = TransitionSystem::new(bdd.clone());

        // Declare cell variables (2 bits per cell, 9 cells)
        let mut cell_bits = Vec::new();
        let mut cell_bits_next = Vec::new();

        for i in 0..9 {
            let lo = Var::new(format!("c{}_lo", i));
            let hi = Var::new(format!("c{}_hi", i));
            ts.declare_var(lo.clone());
            ts.declare_var(hi.clone());

            let lo_p = ts.var_manager().get_present(&lo).unwrap();
            let hi_p = ts.var_manager().get_present(&hi).unwrap();
            let lo_n = ts.var_manager().get_next(&lo).unwrap();
            let hi_n = ts.var_manager().get_next(&hi).unwrap();

            cell_bits.push((bdd.mk_var(lo_p), bdd.mk_var(hi_p)));
            cell_bits_next.push((bdd.mk_var(lo_n), bdd.mk_var(hi_n)));
        }

        // Declare turn variable
        let turn_var = Var::new("turn");
        ts.declare_var(turn_var.clone());

        let turn_p = ts.var_manager().get_present(&turn_var).unwrap();
        let turn_n = ts.var_manager().get_next(&turn_var).unwrap();
        let turn = bdd.mk_var(turn_p);
        let turn_next = bdd.mk_var(turn_n);

        TicTacToeModel {
            bdd,
            ts,
            cell_bits,
            cell_bits_next,
            turn,
            turn_next,
        }
    }

    /// Build BDD for: cell i contains mark m
    fn cell_is(&self, cell: usize, mark: u8) -> Ref {
        let (lo, hi) = self.cell_bits[cell];
        let lo_val = (mark & 1) != 0;
        let hi_val = (mark & 2) != 0;

        let lo_bdd = if lo_val { lo } else { self.bdd.apply_not(lo) };
        let hi_bdd = if hi_val { hi } else { self.bdd.apply_not(hi) };

        self.bdd.apply_and(lo_bdd, hi_bdd)
    }

    /// Build BDD for: cell i contains mark m (next state)
    fn cell_is_next(&self, cell: usize, mark: u8) -> Ref {
        let (lo, hi) = self.cell_bits_next[cell];
        let lo_val = (mark & 1) != 0;
        let hi_val = (mark & 2) != 0;

        let lo_bdd = if lo_val { lo } else { self.bdd.apply_not(lo) };
        let hi_bdd = if hi_val { hi } else { self.bdd.apply_not(hi) };

        self.bdd.apply_and(lo_bdd, hi_bdd)
    }

    /// Build BDD for: cell i stays unchanged
    fn cell_unchanged(&self, cell: usize) -> Ref {
        let (lo, hi) = self.cell_bits[cell];
        let (lo_n, hi_n) = self.cell_bits_next[cell];

        self.bdd.apply_and(self.bdd.apply_eq(lo_n, lo), self.bdd.apply_eq(hi_n, hi))
    }

    /// Build BDD for: it's X's turn
    fn x_turn(&self) -> Ref {
        self.bdd.apply_not(self.turn)
    }

    /// Build BDD for: it's O's turn
    fn o_turn(&self) -> Ref {
        self.turn
    }

    /// Check if player has won (3 in a row)
    fn player_wins(&self, mark: u8) -> Ref {
        // Winning lines: rows, columns, diagonals
        let lines = [
            [0, 1, 2], // Row 0
            [3, 4, 5], // Row 1
            [6, 7, 8], // Row 2
            [0, 3, 6], // Col 0
            [1, 4, 7], // Col 1
            [2, 5, 8], // Col 2
            [0, 4, 8], // Diag
            [2, 4, 6], // Anti-diag
        ];

        let mut wins = self.bdd.zero();
        for line in &lines {
            let line_complete = self.bdd.apply_and(
                self.cell_is(line[0], mark),
                self.bdd.apply_and(self.cell_is(line[1], mark), self.cell_is(line[2], mark)),
            );
            wins = self.bdd.apply_or(wins, line_complete);
        }
        wins
    }

    /// Check if board is full
    fn board_full(&self) -> Ref {
        let mut full = self.bdd.one();
        for i in 0..9 {
            let cell_occupied = self.bdd.apply_not(self.cell_is(i, EMPTY));
            full = self.bdd.apply_and(full, cell_occupied);
        }
        full
    }

    /// Build the complete game model
    fn build(&mut self) {
        // Initial state: empty board, X's turn
        let mut initial = self.bdd.one();
        for i in 0..9 {
            initial = self.bdd.apply_and(initial, self.cell_is(i, EMPTY));
        }
        initial = self.bdd.apply_and(initial, self.x_turn());
        self.ts.set_initial(initial);

        // Transition relation: place mark in empty cell, switch turn
        // Only if game not already over

        let x_wins = self.player_wins(X_MARK);
        let o_wins = self.player_wins(O_MARK);
        let game_over = self.bdd.apply_or(x_wins, o_wins);
        let game_not_over = self.bdd.apply_not(game_over);

        let mut all_moves = self.bdd.zero();

        // X's moves (when it's X's turn and game not over)
        let x_can_move = self.bdd.apply_and(self.x_turn(), game_not_over);
        for cell in 0..9 {
            // Guard: cell is empty
            let cell_empty = self.cell_is(cell, EMPTY);
            let guard = self.bdd.apply_and(x_can_move, cell_empty);

            // Effect: place X in cell, switch turn, others unchanged
            let mut effect = self.cell_is_next(cell, X_MARK);
            effect = self.bdd.apply_and(effect, self.turn_next); // O's turn next

            for other in 0..9 {
                if other != cell {
                    effect = self.bdd.apply_and(effect, self.cell_unchanged(other));
                }
            }

            let x_move = self.bdd.apply_and(guard, effect);
            all_moves = self.bdd.apply_or(all_moves, x_move);
        }

        // O's moves (when it's O's turn and game not over)
        let o_can_move = self.bdd.apply_and(self.o_turn(), game_not_over);
        for cell in 0..9 {
            let cell_empty = self.cell_is(cell, EMPTY);
            let guard = self.bdd.apply_and(o_can_move, cell_empty);

            let mut effect = self.cell_is_next(cell, O_MARK);
            effect = self.bdd.apply_and(effect, self.bdd.apply_not(self.turn_next)); // X's turn next

            for other in 0..9 {
                if other != cell {
                    effect = self.bdd.apply_and(effect, self.cell_unchanged(other));
                }
            }

            let o_move = self.bdd.apply_and(guard, effect);
            all_moves = self.bdd.apply_or(all_moves, o_move);
        }

        // Terminal states loop (game over states have self-loops)
        let board_full = self.board_full();
        let game_ended = self.bdd.apply_or(game_over, board_full);

        // Self-loop: all cells stay, turn stays
        let mut self_loop = self.bdd.apply_eq(self.turn_next, self.turn);
        for cell in 0..9 {
            self_loop = self.bdd.apply_and(self_loop, self.cell_unchanged(cell));
        }
        let terminal_loop = self.bdd.apply_and(game_ended, self_loop);

        all_moves = self.bdd.apply_or(all_moves, terminal_loop);
        self.ts.set_transition(all_moves);

        // Add labels
        self.ts.add_label("x_wins".to_string(), x_wins);
        self.ts.add_label("o_wins".to_string(), o_wins);

        let draw_state = self
            .bdd
            .apply_and(board_full, self.bdd.apply_not(self.bdd.apply_or(x_wins, o_wins)));
        self.ts.add_label("draw".to_string(), draw_state);

        self.ts.add_label("x_turn".to_string(), self.x_turn());
        self.ts.add_label("o_turn".to_string(), self.o_turn());
        self.ts.add_label("game_over".to_string(), game_ended);
    }

    /// Compute attractor for player towards goal.
    ///
    /// Attractor = set of states from which player can force reaching goal.
    ///
    /// For the moving player at state s:
    /// - If it's our turn: we can reach goal if ANY move leads to attractor
    /// - If opponent's turn: we reach goal only if ALL moves lead to attractor
    fn compute_attractor(&self, player_turn: Ref, goal: Ref) -> Ref {
        // opponent_turn = NOT player_turn
        let opponent_turn = self.bdd.apply_not(player_turn);

        // Start with goal states
        let mut attractor = goal;

        loop {
            // States where it's our turn and we can move to attractor
            // (exists a successor in attractor)
            let our_turn_can_reach = self.bdd.apply_and(player_turn, self.ts.preimage(attractor));

            // States where it's opponent's turn and ALL moves lead to attractor
            // This is: opponent_turn AND NOT(exists move to NOT attractor)
            let not_attractor = self.bdd.apply_not(attractor);
            let can_escape = self.ts.preimage(not_attractor);
            let opponent_forced = self.bdd.apply_and(opponent_turn, self.bdd.apply_not(can_escape));

            // Union of goal + our forced + opponent forced
            let new_attractor = self.bdd.apply_or(goal, self.bdd.apply_or(our_turn_can_reach, opponent_forced));

            if new_attractor == attractor {
                return attractor;
            }
            attractor = new_attractor;
        }
    }

    fn get_ts(&self) -> &TransitionSystem {
        &self.ts
    }

    fn get_bdd(&self) -> &Bdd {
        &self.bdd
    }
}

fn main() {
    println!("Tic-Tac-Toe - Game Solving with Attractor Computation");
    println!("═════════════════════════════════════════════════════\n");

    println!("Analyzing the classic 3x3 Tic-Tac-Toe game to determine");
    println!("winning, losing, and drawing positions for each player.\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 1: Build the Game Model
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 1: Building the game model");

    let mut model = TicTacToeModel::new();
    model.build();
    let ts = model.get_ts();
    let bdd = model.get_bdd();

    println!("  Board: 3x3 grid (9 cells)");
    println!("  Cell encoding: 2 bits (Empty=00, X=01, O=10)");
    println!("  Turn: 1 bit (X=0, O=1)");
    println!("  Total variables: 19 boolean\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 2: State Space Analysis
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 2: Analyzing state space");

    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    // Maximum theoretical: 3^9 * 2 = 39366 (but many are invalid game states)
    println!("  Theoretical maximum: 3^9 × 2 = 39,366");

    if let Some(count) = state_count {
        println!("  Reachable game states: {}", count);
        assert!(count > 0, "Must have reachable states");
        assert!(count < 39366, "Not all encodings are valid game states");
        println!("  ✓ State space explored\n");
    }

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 3: Terminal State Analysis
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 3: Analyzing terminal states");

    let x_wins = ts.get_label("x_wins").unwrap();
    let o_wins = ts.get_label("o_wins").unwrap();
    let draw = ts.get_label("draw").unwrap();

    // Count terminal states that are reachable
    let x_wins_reachable = bdd.apply_and(x_wins, reachable);
    let o_wins_reachable = bdd.apply_and(o_wins, reachable);
    let draw_reachable = bdd.apply_and(draw, reachable);

    let x_win_count = ts.count_states(x_wins_reachable).unwrap_or(0);
    let o_win_count = ts.count_states(o_wins_reachable).unwrap_or(0);
    let draw_count = ts.count_states(draw_reachable).unwrap_or(0);

    println!("  X-wins positions:  {} reachable", x_win_count);
    println!("  O-wins positions:  {} reachable", o_win_count);
    println!("  Draw positions:    {} reachable", draw_count);

    assert!(x_win_count > 0, "X must have some winning positions");
    assert!(o_win_count > 0, "O must have some winning positions");
    assert!(draw_count > 0, "There must be draw positions");

    println!("  ✓ Terminal states identified\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 4: Attractor Computation
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 4: Computing attractors (winning regions)");

    println!("  Attractor = states from which a player can FORCE a win,");
    println!("  assuming optimal play from both sides.\n");

    // X's winning region: states from which X can force reaching x_wins
    let x_turn = ts.get_label("x_turn").unwrap();
    let o_turn = ts.get_label("o_turn").unwrap();

    println!("─── Computing X's Winning Region ───");
    println!("States from which X can force a win...\n");

    let x_winning_region = model.compute_attractor(x_turn, x_wins);
    let x_winning_reachable = bdd.apply_and(x_winning_region, reachable);
    let x_region_count = ts.count_states(x_winning_reachable).unwrap_or(0);

    println!("  X-winning region: {} reachable states", x_region_count);

    println!("\n─── Computing O's Winning Region ───");
    println!("States from which O can force a win...\n");

    let o_winning_region = model.compute_attractor(o_turn, o_wins);
    let o_winning_reachable = bdd.apply_and(o_winning_region, reachable);
    let o_region_count = ts.count_states(o_winning_reachable).unwrap_or(0);

    println!("  O-winning region: {} reachable states", o_region_count);

    // Drawing region: reachable states not in either winning region
    let any_winning = bdd.apply_or(x_winning_region, o_winning_region);
    let drawing_region = bdd.apply_and(reachable, bdd.apply_not(any_winning));
    let draw_region_count = ts.count_states(drawing_region).unwrap_or(0);

    println!("\n─── Drawing Region ───");
    println!("States where best play leads to a draw...\n");
    println!("  Drawing region: {} reachable states", draw_region_count);
    println!();

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 5: Initial Position Analysis
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 5: Analyzing the initial position");

    let initial = ts.initial();

    let initial_in_x_win = !bdd.is_zero(bdd.apply_and(initial, x_winning_region));
    let initial_in_o_win = !bdd.is_zero(bdd.apply_and(initial, o_winning_region));
    let initial_in_draw = !bdd.is_zero(bdd.apply_and(initial, drawing_region));

    println!("  Empty board (X to move):");
    println!("  - In X's winning region?  {}", if initial_in_x_win { "YES" } else { "NO" });
    println!("  - In O's winning region?  {}", if initial_in_o_win { "YES" } else { "NO" });
    println!("  - In drawing region?      {}", if initial_in_draw { "YES" } else { "NO" });
    println!();

    // The famous result: Tic-Tac-Toe is a draw with perfect play
    if initial_in_draw && !initial_in_x_win && !initial_in_o_win {
        println!("  ★ CLASSIC RESULT CONFIRMED:");
        println!("    Tic-Tac-Toe is a DRAW with perfect play from both sides!");
        println!("    Neither X nor O can force a win from the empty board.\n");
    } else if initial_in_x_win {
        println!("  Result: X can force a win from the empty board.\n");
    } else if initial_in_o_win {
        println!("  Result: O can force a win from the empty board.\n");
    }

    // Verify the expected result
    assert!(
        initial_in_draw,
        "Initial position should be in drawing region (perfect play = draw)"
    );
    assert!(!initial_in_x_win, "X should not be able to force win from empty board");
    assert!(!initial_in_o_win, "O should not be able to force win from empty board");

    // ═══════════════════════════════════════════════════════════════════════════
    // Step 6: Strategy Insights
    // ═══════════════════════════════════════════════════════════════════════════

    header("Step 6: Strategy insights");

    // Count winning positions by whose turn it is
    let x_win_on_x_turn = bdd.apply_and(x_winning_reachable, x_turn);
    let x_win_on_o_turn = bdd.apply_and(x_winning_reachable, o_turn);
    let o_win_on_x_turn = bdd.apply_and(o_winning_reachable, x_turn);
    let o_win_on_o_turn = bdd.apply_and(o_winning_reachable, o_turn);

    let x_win_x_turn_count = ts.count_states(x_win_on_x_turn).unwrap_or(0);
    let x_win_o_turn_count = ts.count_states(x_win_on_o_turn).unwrap_or(0);
    let o_win_x_turn_count = ts.count_states(o_win_on_x_turn).unwrap_or(0);
    let o_win_o_turn_count = ts.count_states(o_win_on_o_turn).unwrap_or(0);

    println!("  X's winning region breakdown:");
    println!("    - When it's X's turn: {} positions", x_win_x_turn_count);
    println!("    - When it's O's turn: {} positions (O made a mistake)", x_win_o_turn_count);
    println!();
    println!("  O's winning region breakdown:");
    println!("    - When it's O's turn: {} positions", o_win_o_turn_count);
    println!("    - When it's X's turn: {} positions (X made a mistake)", o_win_x_turn_count);
    println!();

    // ═══════════════════════════════════════════════════════════════════════════
    // Key Insights
    // ═══════════════════════════════════════════════════════════════════════════

    header("Key Insights");

    println!("  1. ATTRACTOR COMPUTATION");
    println!("     - Backward fixpoint from goal states");
    println!("     - Different rules for moving vs waiting player");
    println!("     - Computes optimal strategy implicitly\n");

    println!("  2. GAME-THEORETIC CLASSIFICATION");
    println!("     - Every position is exactly one of: X-win, O-win, Draw");
    println!("     - Classification is based on OPTIMAL play");
    println!("     - Sub-optimal play can change outcomes\n");

    println!("  3. TWO-PLAYER GAME SOLVING");
    println!("     - BDDs represent winning regions symbolically");
    println!("     - No explicit game tree enumeration");
    println!("     - Handles all positions simultaneously\n");

    println!("  4. TIC-TAC-TOE SOLUTION");
    println!("     - Empty board is a DRAW with perfect play");
    println!("     - Neither player has a forced win initially");
    println!("     - Many positions become winning after mistakes\n");

    // ═══════════════════════════════════════════════════════════════════════════
    // Summary
    // ═══════════════════════════════════════════════════════════════════════════

    header("Summary");
    if let Some(count) = state_count {
        println!("  Total reachable states:  {}", count);
    }
    println!("  X-winning region:        {} states", x_region_count);
    println!("  O-winning region:        {} states", o_region_count);
    println!("  Drawing region:          {} states", draw_region_count);
    println!();
    println!("  Initial position: DRAW (with perfect play)");
    println!("  X-win positions: {}", x_win_count);
    println!("  O-win positions: {}", o_win_count);
    println!("  Draw positions:  {}", draw_count);
    println!();

    println!("✓ All assertions passed! Tic-Tac-Toe game solved.\n");
}
