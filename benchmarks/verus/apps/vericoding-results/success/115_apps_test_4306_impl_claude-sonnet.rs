// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

spec fn min(x: int, y: int) -> int {
    if x < y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x > y { x } else { y }
}

spec fn interval_overlap_length(a: int, b: int, c: int, d: int) -> int {
    if min(b, d) - max(a, c) > 0 { min(b, d) - max(a, c) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// Lemma to prove that max result is within bounds
proof fn lemma_max_bounds(a: int, b: int) -> (result: int)
    requires
        0 <= a <= 100,
        0 <= b <= 100,
    ensures
        result == max(a, b),
        0 <= result <= 100,
{
    max(a, b)
}

// Lemma to prove that min result is within bounds
proof fn lemma_min_bounds(a: int, b: int) -> (result: int)
    requires
        0 <= a <= 100,
        0 <= b <= 100,
    ensures
        result == min(a, b),
        0 <= result <= 100,
{
    min(a, b)
}

// Lemma to prove overlap length is non-negative and bounded
proof fn lemma_overlap_bounds(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        0 <= interval_overlap_length(a, b, c, d) <= 100,
{
    let max_start = max(a, c);
    let min_end = min(b, d);
    
    assert(max_start >= 0);
    assert(min_end <= 100);
    assert(interval_overlap_length(a, b, c, d) >= 0);
    assert(interval_overlap_length(a, b, c, d) <= 100);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        result >= 0,
        result as int == interval_overlap_length(a as int, b as int, c as int, d as int),
        result <= 100,
// </vc-spec>
// <vc-code>
{
    let max_start = if a > c { a } else { c };
    let min_end = if b < d { b } else { d };
    
    let overlap = if min_end > max_start { min_end - max_start } else { 0 };
    
    proof {
        lemma_overlap_bounds(a as int, b as int, c as int, d as int);
        
        assert(max_start as int == max(a as int, c as int));
        assert(min_end as int == min(b as int, d as int));
        assert(overlap as int == interval_overlap_length(a as int, b as int, c as int, d as int));
    }
    
    overlap
}
// </vc-code>


}

fn main() {}