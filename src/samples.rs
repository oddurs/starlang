use crate::lens::SpokeId;

pub struct SamplePreset {
    pub id: &'static str,
    pub title: &'static str,
    pub description: &'static str,
    pub initial_spoke: SpokeId,
    pub source: &'static str,
}

pub const SAMPLES: &[SamplePreset] = &[
    SamplePreset {
        id: "scores",
        title: "Score Clamper & Summary",
        description: "Structs, Rust borrowed &[i64] slices preserved across Swift/C++/Go/Py/TS edits & live unit tests",
        initial_spoke: SpokeId::Rust,
        source: r#"// Aggregate statistics over clamped scores
#[derive(Debug, Clone, PartialEq)]
pub struct Summary {
    pub count: i64,
    pub total: i64,
    pub average: i64,
}

// Clamp every score into [0, limit] using a borrowed Rust slice
pub fn clamp_scores(scores: &[i64], limit: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    for s in scores.iter().cloned() {
        // Floor negative values at zero
        let clamped = s.min(limit).max(0);
        out.push(clamped);
    }
    return out;
}

pub fn summarize(scores: &[i64]) -> Summary {
    let mut total = 0;
    let count = scores.len() as i64;
    for s in scores.iter().cloned() {
        total += s;
    }
    let mut avg = 0;
    if count > 0 {
        avg = total / count;
    }
    return Summary { count: count, total: total, average: avg };
}

fn main() {
    let raw = vec![-15, 40, 85, 130, 95];
    let clean = clamp_scores(&raw, 100);
    let stats = summarize(&clean);
    println!("{} {} {}", "count:", stats.count, stats.total);
    println!("{} {}", "average:", stats.average);
}

#[test]
fn test_clamp_and_summarize() {
    let sample = vec![-5, 50, 120];
    let clamped = clamp_scores(&sample, 100);
    assert_eq!(clamped, vec![0, 50, 100]);
    let summary = summarize(&clamped);
    assert_eq!(summary, Summary { count: 3, total: 150, average: 50 });
}
"#,
    },
    SamplePreset {
        id: "alerts",
        title: "Latency Alert Classifier (Enums & Match)",
        description: "Enums, match/switch dispatch, loop break circuit-breaker, and polyglot assertions",
        initial_spoke: SpokeId::Rust,
        source: r#"// Health state for an upstream service endpoint
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Ok,
    Warn,
    Critical,
}

pub fn classify_latency(ms: i64) -> Severity {
    if ms >= 500 {
        return Severity::Critical;
    } else if ms >= 200 {
        return Severity::Warn;
    } else {
        return Severity::Ok;
    }
}

pub fn severity_weight(sev: Severity) -> i64 {
    match sev {
        Severity::Ok => {
            return 0;
        }
        Severity::Warn => {
            return 1;
        }
        Severity::Critical => {
            return 5;
        }
    }
}

pub fn evaluate_window(latencies: &[i64], budget: i64) -> String {
    let mut score = 0;
    let mut processed = 0;
    for ms in latencies.iter().cloned() {
        if ms < 0 {
            continue;
        }
        let sev = classify_latency(ms);
        score += severity_weight(sev);
        processed += 1;
        // Trip circuit breaker early once error budget is exceeded
        if score >= budget {
            break;
        }
    }
    return format!("{}{}", format!("{}{}", format!("{}{}", "checked=", format!("{}", processed)), " score="), format!("{}", score));
}

fn main() {
    let samples = vec![80, -1, 240, 610, 520, 90];
    let report = evaluate_window(&samples, 6);
    println!("{}", report);
}

#[test]
fn test_alert_thresholds() {
    assert_eq!(classify_latency(95), Severity::Ok);
    assert_eq!(classify_latency(240), Severity::Warn);
    let probe = vec![80, 240];
    assert_eq!(evaluate_window(&probe, 6), "checked=2 score=1".to_string());
}
"#,
    },
    SamplePreset {
        id: "collatz",
        title: "Collatz Stopping-Time Explorer",
        description: "Range loops (0..n <-> Swift stride <-> Go/C++/TS for;; <-> Python range) & live tests",
        initial_spoke: SpokeId::Python,
        source: r#"# Count Collatz hailstone steps needed to reach 1
def collatz_steps(start: int) -> int:
    n = start
    steps = 0
    while n > 1:
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
        steps += 1
    return steps


# Find the longest Collatz chain below upper_bound
def max_collatz_in_range(upper_bound: int) -> int:
    best = 0
    for k in range(1, upper_bound):
        best = max(best, collatz_steps(k))
    return best


def main() -> None:
    print("steps(27):", collatz_steps(27))
    print("max_below_50:", max_collatz_in_range(50))


def test_collatz_known_chains() -> None:
    assert collatz_steps(1) == 0
    assert collatz_steps(6) == 8
    assert max_collatz_in_range(10) == 19


if __name__ == "__main__":
    main()
"#,
    },
    SamplePreset {
        id: "tags",
        title: "Tag Normalizer & Substring Filter",
        description: "String & list intrinsics (.to_lowercase <-> .lowercased <-> strings.ToLower <-> .lower)",
        initial_spoke: SpokeId::Rust,
        source: r#"// Normalize tags to lowercase and keep only entries matching query
pub fn filter_tags(tags: &[String], query: &str) -> Vec<String> {
    let mut matched: Vec<String> = Vec::new();
    let needle = query.to_lowercase();
    for tag in tags.iter().cloned() {
        let clean = tag.to_lowercase();
        if clean.contains(&needle) {
            matched.push(clean);
        }
    }
    return matched;
}

fn main() {
    let tags = vec!["RustLang".to_string(), "Golang".to_string(), "Python".to_string(), "RustFmt".to_string()];
    let hits = filter_tags(&tags, "rust");
    println!("{} {}", "matches:", hits.len() as i64);
    for h in hits.iter().cloned() {
        println!("{}", h);
    }
}

#[test]
fn test_case_insensitive_tag_filter() {
    let items = vec!["SwiftSix".to_string(), "RustCore".to_string(), "SwiftUI".to_string()];
    let found = filter_tags(&items, "SWIFT");
    assert_eq!(found, vec!["swiftsix".to_string(), "swiftui".to_string()]);
}
"#,
    },
    SamplePreset {
        id: "pipeline",
        title: "Signal Pipeline & Hub Optimizer Lab (Seeded from C++)",
        description: "Try 'Optimize Hub' & 'Trace & Coverage' — folds constants & prunes dead branches across all 8 languages",
        initial_spoke: SpokeId::Cpp,
        source: r#"#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>

// Calibrate sensor readings with foldable constants and algebraic identities
int64_t calibrate_reading(int64_t sample) {
    const auto ceiling = int64_t(25 * 4);
    const auto adjusted = (sample + 0) * 1;
    if (false) {
        return int64_t(-999);
    }
    return std::min(adjusted, ceiling);
}

int main() {
    const auto readings = std::vector<int64_t>{12, 85, 140, 64};
    auto total = int64_t(0);
    for (const auto& r : readings) {
        total += calibrate_reading(r);
    }
    std::cout << "calibrated_sum:" << " " << total << "\n";
    return 0;
}

void test_calibration_ceiling() {
    assert(calibrate_reading(int64_t(42)) == int64_t(42));
    assert(calibrate_reading(int64_t(180)) == int64_t(100));
}
"#,
    },
    SamplePreset {
        id: "ledger",
        title: "Token Bucket Rate-Limiter (Seeded from Swift 6)",
        description: "Pure-stdlib Swift 6 structs, Equatable assertions, field mutation & 8-language sync",
        initial_spoke: SpokeId::Swift,
        source: r#"// Token bucket state for API request throttling
struct BucketState: Equatable {
    var tokens: Int
    var accepted: Int
    var rejected: Int
}

func simulate_burst(_ capacity: Int, _ costs: [Int]) -> BucketState {
    var state = BucketState(tokens: capacity, accepted: 0, rejected: 0)
    for cost in costs {
        if cost <= state.tokens {
            state.tokens -= cost
            state.accepted += 1
        } else {
            state.rejected += 1
        }
    }
    return state
}

func main() {
    let traffic = [4, 5, 6, 3, 2]
    let outcome = simulate_burst(12, traffic)
    print("accepted:", outcome.accepted, "rejected:", outcome.rejected, "left:", outcome.tokens)
}

func test_token_bucket_burst() {
    let burst = [3, 4, 6, 2]
    let result = simulate_burst(8, burst)
    assert(result == BucketState(tokens: 1, accepted: 2, rejected: 2))
    assert(result.tokens >= 0)
}

main()
"#,
    },
    SamplePreset {
        id: "histogram",
        title: "Latency Bucket Histogram (Seeded from Java 21)",
        description: "Modern Java 21 switch arrows, static value classes, Objects.equals assertions & 8-language sync",
        initial_spoke: SpokeId::Java,
        source: r#"import java.util.*;

class StarProgram {
    // Latency tier classification for SLA telemetry
    enum Tier {
        Fast,
        Moderate,
        Slow
    }

    static final class Histogram {
        long fast;
        long moderate;
        long slow;

        Histogram(long fast, long moderate, long slow) {
            this.fast = fast;
            this.moderate = moderate;
            this.slow = slow;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof Histogram other)) return false;
            return Objects.equals(this.fast, other.fast) && Objects.equals(this.moderate, other.moderate) && Objects.equals(this.slow, other.slow);
        }

        @Override
        public int hashCode() {
            return Objects.hash(this.fast, this.moderate, this.slow);
        }
    }

    static Tier classify_ms(long ms) {
        if (ms < 50L) {
            return Tier.Fast;
        } else if (ms < 200L) {
            return Tier.Moderate;
        } else {
            return Tier.Slow;
        }
    }

    static Histogram build_histogram(List<Long> samples) {
        var hist = new Histogram(0L, 0L, 0L);
        for (final var ms : samples) {
            final var tier = classify_ms(ms);
            switch (tier) {
                case Tier.Fast -> {
                    hist.fast += 1L;
                }
                case Tier.Moderate -> {
                    hist.moderate += 1L;
                }
                case Tier.Slow -> {
                    hist.slow += 1L;
                }
            }
        }
        return hist;
    }

    public static void main(String[] args) {
        final var latencies = new ArrayList<>(Arrays.asList(18L, 42L, 95L, 240L, 12L, 310L));
        final var h = build_histogram(latencies);
        System.out.println(String.join(" ", String.valueOf("fast:"), String.valueOf(h.fast), String.valueOf("mod:"), String.valueOf(h.moderate), String.valueOf("slow:"), String.valueOf(h.slow)));
    }

    static void test_histogram_buckets() {
        final var probe = new ArrayList<>(Arrays.asList(10L, 80L, 250L, 35L));
        final var res = build_histogram(probe);
        if (!Objects.equals(res, new Histogram(2L, 1L, 1L))) throw new AssertionError("assert_eq failed");
    }
}
"#,
    },
];

pub fn find_sample(id: &str) -> Option<&'static SamplePreset> {
    SAMPLES.iter().find(|s| s.id == id)
}
