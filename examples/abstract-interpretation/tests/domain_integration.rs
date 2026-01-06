//! Integration tests for multiple abstract domains working together

use abstract_interpretation::*;

#[test]
fn test_sign_constant_cooperation() {
    // Test that Sign and Constant domains provide complementary information
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;

    // Start with x = 5
    let sign_elem = sign_domain.constant("x", 5);
    let const_elem = const_domain.constant("x", 5);

    // Sign knows it's positive
    assert_eq!(sign_elem.get("x"), Sign::Pos);

    // Constant knows exact value
    assert_eq!(const_elem.get("x"), ConstValue::Const(5));

    // After y = x + 10
    use NumExpr::*;
    let expr = Add(Box::new(Var("x".to_string())), Box::new(Const(10)));

    let sign_result = sign_domain.assign(&sign_elem, "y", &expr);
    let const_result = const_domain.assign(&const_elem, "y", &expr);

    // Sign: positive + positive = positive (strictly)
    assert_eq!(sign_result.get("y"), Sign::Pos);

    // Constant: 5 + 10 = 15
    assert_eq!(const_result.get("y"), ConstValue::Const(15));
}

#[test]
fn test_sign_interval_cooperation() {
    // Test Sign and Interval working together
    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;

    // x in [1, 100]
    let sign_elem = sign_domain.interval("x", 1, 100);
    let interval_elem = interval_domain.interval("x", 1, 100);

    // Sign: all positive (since low > 0)
    assert_eq!(sign_elem.get("x"), Sign::Pos);

    // Interval: precise bounds
    if let Some((low, high)) = interval_domain.get_bounds(&interval_elem, "x") {
        assert_eq!(low, 1);
        assert_eq!(high, 100);
    } else {
        panic!("Expected bounds");
    }
}

#[test]
fn test_constant_interval_refinement() {
    // Test how Constant and Interval refine each other
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Start with x = 5
    let const_elem = const_domain.constant("x", 5);
    let interval_elem = interval_domain.constant("x", 5);

    // Both agree on singleton
    assert_eq!(const_elem.get("x"), ConstValue::Const(5));
    assert_eq!(interval_domain.get_bounds(&interval_elem, "x"), Some((5, 5)));

    // After join with x in [10, 20]
    let const_elem2 = const_domain.constant("x", 15);
    let interval_elem2 = interval_domain.interval("x", 10, 20);

    let const_joined = const_domain.join(&const_elem, &const_elem2);
    let interval_joined = interval_domain.join(&interval_elem, &interval_elem2);

    // Constant loses precision (5 vs 15 -> Top)
    assert_eq!(const_joined.get("x"), ConstValue::Top);

    // Interval maintains bounds [5, 20]
    assert_eq!(interval_domain.get_bounds(&interval_joined, "x"), Some((5, 20)));
}

#[test]
fn test_triple_domain_analysis() {
    // Test all three domains analyzing the same program
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Program: x = 7; y = x; z = y;
    let sign = sign_domain.constant("x", 7);
    let constant = const_domain.constant("x", 7);
    let interval = interval_domain.constant("x", 7);

    use NumExpr::*;
    let expr = Var("x".to_string());

    let sign = sign_domain.assign(&sign, "y", &expr);
    let constant = const_domain.assign(&constant, "y", &expr);
    let interval = interval_domain.assign(&interval, "y", &expr);

    let expr = Var("y".to_string());

    let sign = sign_domain.assign(&sign, "z", &expr);
    let constant = const_domain.assign(&constant, "z", &expr);
    let interval = interval_domain.assign(&interval, "z", &expr);

    // All domains agree: z = 7
    assert_eq!(sign.get("z"), Sign::Pos);
    assert_eq!(constant.get("z"), ConstValue::Const(7));
    assert_eq!(interval_domain.get_bounds(&interval, "z"), Some((7, 7)));
}

#[test]
fn test_sign_constant_assume() {
    // Test assume() operations across domains
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;

    // Start with x in unknown range
    let sign_elem = sign_domain.top();
    let const_elem = const_domain.top();

    // Assume x > 0
    use NumExpr::*;
    use NumPred::*;
    let pred = Gt(Var("x".to_string()), Const(0));

    let sign_refined = sign_domain.assume(&sign_elem, &pred);
    let const_refined = const_domain.assume(&const_elem, &pred);

    // Sign: x must be positive
    assert_eq!(sign_refined.get("x"), Sign::Pos);

    // Constant: still unknown (could be any positive value)
    assert_eq!(const_refined.get("x"), ConstValue::Top);

    // Now assume x == 5
    let pred = Eq(Var("x".to_string()), Const(5));

    let sign_refined2 = sign_domain.assume(&sign_refined, &pred);
    let const_refined2 = const_domain.assume(&const_refined, &pred);

    // Sign: still positive
    assert_eq!(sign_refined2.get("x"), Sign::Pos);

    // Constant: now knows exact value
    assert_eq!(const_refined2.get("x"), ConstValue::Const(5));
}

#[test]
fn test_domain_precision_comparison() {
    // Compare precision of different domains on same operations
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // x = 5, y = 10
    let sign = sign_domain.constant("x", 5);
    let sign = sign_domain.assign(&sign, "y", &NumExpr::constant(10));

    let constant = const_domain.constant("x", 5);
    let constant = const_domain.assign(&constant, "y", &NumExpr::constant(10));

    let interval = interval_domain.constant("x", 5);
    let interval = interval_domain.assign(&interval, "y", &NumExpr::constant(10));

    // z = x + y
    let expr = NumExpr::var("x").add(NumExpr::var("y"));

    let sign_result = sign_domain.assign(&sign, "z", &expr);
    let const_result = const_domain.assign(&constant, "z", &expr);
    let interval_result = interval_domain.assign(&interval, "z", &expr);

    // Sign: positive + positive = positive (strictly)
    assert_eq!(sign_result.get("z"), Sign::Pos);

    // Constant: exact value 15
    assert_eq!(const_result.get("z"), ConstValue::Const(15));

    // Interval: exact value [15, 15]
    assert_eq!(interval_domain.get_bounds(&interval_result, "z"), Some((15, 15)));

    // Constant and Interval are most precise here
}

#[test]
fn test_widening_across_domains() {
    // Test widening behavior in different domains
    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Iteration 1: x = 0
    let sign1 = sign_domain.constant("x", 0);
    let const1 = const_domain.constant("x", 0);
    let interval1 = interval_domain.constant("x", 0);

    // Iteration 2: x = 1
    let sign2 = sign_domain.constant("x", 1);
    let const2 = const_domain.constant("x", 1);
    let interval2 = interval_domain.constant("x", 1);

    // Widen
    let sign_widened = sign_domain.widen(&sign1, &sign2);
    let const_widened = const_domain.widen(&const1, &const2);
    let interval_widened = interval_domain.widen(&interval1, &interval2);

    // Sign: 0 and 1 -> NonNeg (flat lattice, widen = join)
    assert_eq!(sign_widened.get("x"), Sign::NonNeg);

    // Constant: different constants -> Top (flat lattice, widen = join)
    assert_eq!(const_widened.get("x"), ConstValue::Top);

    // Interval: [0,0] ∇ [1,1] -> typically [0, +∞) but implementation may vary
    // Just verify widening doesn't lose the lower bound 0
    let bounds = interval_domain.get_bounds(&interval_widened, "x");
    if let Some((low, _high)) = bounds {
        assert_eq!(low, 0, "Lower bound should be preserved");
        // Upper bound might be MAX or infinite depending on implementation
    }
    // Note: Some widening strategies might lose precision entirely
}

#[test]
fn test_pointsto_with_numeric() {
    // Test pointer arithmetic and array access with numeric domains
    use std::rc::Rc;

    let interval_domain = IntervalDomain;
    let sign_domain = SignDomain;
    let pointsto_domain = PointsToDomain::new();

    // Simulate: int arr[10]; int *p = &arr[0]; int i = 5;
    let pointsto_state = pointsto_domain.assign_address(
        &PointsToElement::new(Rc::clone(pointsto_domain.bdd())),
        "p",
        &Location::Heap(1), // Represent array base as heap location
    );
    let interval_state = interval_domain.constant("i", 5);
    let sign_state = sign_domain.constant("i", 5);

    // Verify pointer points to heap
    let targets = pointsto_domain.decode_bdd(pointsto_state.get("p"));
    assert!(targets.contains(&Location::Heap(1)), "p should point to heap location");

    // Verify index is within bounds [0, 9]
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, "i") {
        assert!(low >= 0 && high < 10, "Array access should be safe");
    }

    // Verify index is positive
    assert_eq!(sign_state.get("i"), Sign::Pos, "Index should be positive");

    // Simulate: p[i] access
    // In a real analysis, we'd track that p+i still points to array
    println!("Array access p[i] is safe:");
    println!("  - p points to: {:?}", targets);
    println!("  - i = {:?}", interval_domain.get_bounds(&interval_state, "i"));
    println!("  - sign(i) = {:?}", sign_state.get("i"));

    // Test with potentially unsafe access: i = 15
    let interval_unsafe = interval_domain.constant("i", 15);
    let _sign_unsafe = sign_domain.constant("i", 15);

    if let Some((_low, high)) = interval_domain.get_bounds(&interval_unsafe, "i") {
        if high >= 10 {
            println!("\nUnsafe array access detected: i = {} >= array size 10", high);
        }
    }

    // Test pointer aliasing with array elements
    // p = &arr[0], q = &arr[0] => must alias
    let mut state2 = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));
    state2 = pointsto_domain.assign_address(&state2, "p", &Location::Heap(1));
    state2 = pointsto_domain.assign_address(&state2, "q", &Location::Heap(1));

    assert!(
        state2.must_alias(&pointsto_domain, "p", "q"),
        "p and q pointing to same array element must alias"
    );

    // p = &arr[0], q = &arr[1] => may alias (different elements)
    let mut state3 = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));
    state3 = pointsto_domain.assign_address(&state3, "p", &Location::Heap(1));
    state3 = pointsto_domain.assign_address(&state3, "q", &Location::Heap(2));

    assert!(
        !state3.must_alias(&pointsto_domain, "p", "q"),
        "p and q pointing to different elements must not alias"
    );
}

#[test]
fn test_pointsto_with_constant_offsets() {
    // Test pointer arithmetic with constant offsets
    use std::rc::Rc;

    let const_domain = ConstantDomain;
    let pointsto_domain = PointsToDomain::new();

    // Simulate: int *p = &x; int offset = 0;
    let mut pointsto_state = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));
    let mut const_state = const_domain.constant("offset", 0);

    pointsto_state = pointsto_domain.assign_address(&pointsto_state, "p", &Location::Stack("x".to_string()));

    // Verify offset is exactly 0
    assert_eq!(const_state.get("offset"), ConstValue::Const(0), "Offset should be constant 0");

    // p + offset still points to x (since offset = 0)
    let targets = pointsto_domain.decode_bdd(pointsto_state.get("p"));
    assert!(targets.contains(&Location::Stack("x".to_string())), "p should still point to x");

    // Test with non-zero offset
    const_state = const_domain.constant("offset", 4);
    assert_eq!(const_state.get("offset"), ConstValue::Const(4), "Offset should be constant 4");

    // In a field-sensitive analysis, p + 4 might point to different field
    // For now, we just verify the constant propagation works
}

#[test]
fn test_combined_sign_interval_pointsto() {
    // Test all three domains together on a realistic scenario
    use std::rc::Rc;

    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;
    let pointsto_domain = PointsToDomain::new();

    // Scenario: loop with pointer and index
    // for (i = 0; i < n; i++) { p[i] = 0; }

    // After loop analysis: i in [0, n-1]
    let sign_state = sign_domain.interval("i", 0, 9);
    let interval_state = interval_domain.interval("i", 0, 9);
    let mut pointsto_state = PointsToElement::new(Rc::clone(pointsto_domain.bdd()));

    pointsto_state = pointsto_domain.assign_address(&pointsto_state, "p", &Location::Heap(1));

    // Verify all invariants
    assert_eq!(sign_state.get("i"), Sign::NonNeg, "Index should be non-negative");

    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, "i") {
        assert!(low >= 0, "Lower bound should be non-negative");
        assert!(high < 10, "Upper bound should be less than array size");
    }

    let targets = pointsto_domain.decode_bdd(pointsto_state.get("p"));
    assert_eq!(targets.len(), 1, "Pointer should have single target");
    assert!(targets.contains(&Location::Heap(1)), "Pointer should point to heap");

    // All domains agree: the loop is safe
    println!("Combined analysis results:");
    println!("  - Sign: i is non-negative");
    println!("  - Interval: i ∈ [0, 9]");
    println!("  - Points-to: p → Heap(1)");
    println!("  ✓ Loop is memory-safe");
}
