//! Performance metrics for incremental operations.
//!
//! This module provides types for collecting and reporting metrics
//! about incremental vs full recomputation performance.

use std::time::{Duration, Instant};

/// Metrics collected during incremental operations.
#[derive(Debug, Clone, Default)]
pub struct IncrementalMetricsData {
    // Time metrics
    /// Time taken for full recomputation.
    pub full_recompute_time: Option<Duration>,
    /// Time taken for incremental update.
    pub incremental_time: Option<Duration>,

    // Node metrics
    /// Number of BDD nodes reused.
    pub nodes_reused: u64,
    /// Number of BDD nodes rebuilt.
    pub nodes_rebuilt: u64,

    // Iteration metrics
    /// Iterations in full recomputation.
    pub full_iterations: usize,
    /// Iterations in incremental update.
    pub incremental_iterations: usize,

    // Effect classification counts
    /// Number of operations that had no change.
    pub no_change_count: usize,
    /// Number of operations with local changes.
    pub local_change_count: usize,
    /// Number of operations requiring global rebuild.
    pub global_rebuild_count: usize,
}

impl IncrementalMetricsData {
    /// Create new empty metrics.
    pub fn new() -> Self {
        Self::default()
    }

    /// Calculate the speedup ratio (full time / incremental time).
    pub fn speedup(&self) -> Option<f64> {
        match (self.full_recompute_time, self.incremental_time) {
            (Some(full), Some(inc)) if !inc.is_zero() => Some(full.as_secs_f64() / inc.as_secs_f64()),
            _ => None,
        }
    }

    /// Calculate the node reuse ratio.
    pub fn reuse_ratio(&self) -> f64 {
        let total = self.nodes_reused + self.nodes_rebuilt;
        if total == 0 {
            1.0
        } else {
            self.nodes_reused as f64 / total as f64
        }
    }

    /// Calculate iteration savings ratio.
    pub fn iteration_savings(&self) -> f64 {
        if self.full_iterations == 0 {
            0.0
        } else {
            1.0 - (self.incremental_iterations as f64 / self.full_iterations as f64)
        }
    }

    /// Get the fraction of operations that were truly incremental.
    pub fn incremental_ratio(&self) -> f64 {
        let total = self.no_change_count + self.local_change_count + self.global_rebuild_count;
        if total == 0 {
            1.0
        } else {
            (self.no_change_count + self.local_change_count) as f64 / total as f64
        }
    }

    /// Generate a summary report.
    pub fn summary(&self) -> String {
        let mut report = String::new();

        report.push_str("=== Incremental Metrics Summary ===\n\n");

        // Time metrics
        if let Some(speedup) = self.speedup() {
            report.push_str(&format!(
                "Time: full={:?}, incremental={:?}, speedup={:.2}x\n",
                self.full_recompute_time.unwrap(),
                self.incremental_time.unwrap(),
                speedup
            ));
        }

        // Node metrics
        report.push_str(&format!(
            "Nodes: reused={}, rebuilt={}, reuse_ratio={:.1}%\n",
            self.nodes_reused,
            self.nodes_rebuilt,
            self.reuse_ratio() * 100.0
        ));

        // Iteration metrics
        report.push_str(&format!(
            "Iterations: full={}, incremental={}, saved={:.1}%\n",
            self.full_iterations,
            self.incremental_iterations,
            self.iteration_savings() * 100.0
        ));

        // Effect classification
        report.push_str(&format!(
            "Effects: no_change={}, local={}, global_rebuild={}\n",
            self.no_change_count, self.local_change_count, self.global_rebuild_count
        ));

        report.push_str(&format!("Incremental ratio: {:.1}%\n", self.incremental_ratio() * 100.0));

        report
    }
}

/// A timer for measuring operation durations.
pub struct MetricsTimer {
    start: Instant,
}

impl MetricsTimer {
    /// Start a new timer.
    pub fn start() -> Self {
        MetricsTimer { start: Instant::now() }
    }

    /// Stop the timer and return the elapsed duration.
    pub fn stop(&self) -> Duration {
        self.start.elapsed()
    }
}

/// Builder for collecting metrics across multiple operations.
#[derive(Debug, Default)]
pub struct MetricsCollector {
    data: IncrementalMetricsData,
    operation_count: usize,
}

impl MetricsCollector {
    /// Create a new metrics collector.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a full recomputation timing.
    pub fn record_full_recompute(&mut self, duration: Duration, iterations: usize) {
        self.data.full_recompute_time = Some(duration);
        self.data.full_iterations = iterations;
    }

    /// Record an incremental update timing.
    pub fn record_incremental(&mut self, duration: Duration, iterations: usize) {
        self.data.incremental_time = Some(duration);
        self.data.incremental_iterations = iterations;
        self.operation_count += 1;
    }

    /// Record node statistics.
    pub fn record_nodes(&mut self, reused: u64, rebuilt: u64) {
        self.data.nodes_reused += reused;
        self.data.nodes_rebuilt += rebuilt;
    }

    /// Record a no-change effect.
    pub fn record_no_change(&mut self) {
        self.data.no_change_count += 1;
    }

    /// Record a local change effect.
    pub fn record_local_change(&mut self) {
        self.data.local_change_count += 1;
    }

    /// Record a global rebuild.
    pub fn record_global_rebuild(&mut self) {
        self.data.global_rebuild_count += 1;
    }

    /// Get the collected metrics.
    pub fn metrics(&self) -> &IncrementalMetricsData {
        &self.data
    }

    /// Consume and return the collected metrics.
    pub fn into_metrics(self) -> IncrementalMetricsData {
        self.data
    }

    /// Get the operation count.
    pub fn operation_count(&self) -> usize {
        self.operation_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reuse_ratio() {
        let mut metrics = IncrementalMetricsData::new();
        metrics.nodes_reused = 75;
        metrics.nodes_rebuilt = 25;

        assert!((metrics.reuse_ratio() - 0.75).abs() < 0.001);
    }

    #[test]
    fn test_speedup() {
        let mut metrics = IncrementalMetricsData::new();
        metrics.full_recompute_time = Some(Duration::from_millis(100));
        metrics.incremental_time = Some(Duration::from_millis(10));

        assert!((metrics.speedup().unwrap() - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_iteration_savings() {
        let mut metrics = IncrementalMetricsData::new();
        metrics.full_iterations = 100;
        metrics.incremental_iterations = 20;

        assert!((metrics.iteration_savings() - 0.8).abs() < 0.001);
    }
}
