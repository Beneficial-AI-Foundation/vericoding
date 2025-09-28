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

proof fn lemma_min_lower_bound(x: int, y: int)
    ensures
        min(x, y) <= x,
        min(x, y) <= y,
{
}

proof fn lemma_max_upper_bound(x: int, y: int)
    ensures
        x <= max(x, y),
        y <= max(x, y),
{
}

proof fn lemma_overlap_bounds(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        max(a, c) >= a,
        max(a, c) >= c,
        min(b, d) <= b,
        min(b, d) <= d,
        a >= 0,
        c >= 0,
        b <= 100,
        d <= 100,
{
    lemma_min_lower_bound(b, d);
    lemma_max_upper_bound(a, c);
}

proof fn lemma_overlap_nonnegative(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        max(a, c) <= min(b, d) ==> min(b, d) - max(a, c) >= 0,
        max(a, c) > min(b, d) ==> 0 >= 0,
{
    lemma_min_lower_bound(b, d);
    lemma_max_upper_bound(a, c);
}

proof fn lemma_overlap_cases(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        min(b, d) - max(a, c) > 0 ==> interval_overlap_length(a, b, c, d) == min(b, d) - max(a, c),
        min(b, d) - max(a, c) <= 0 ==> interval_overlap_length(a, b, c, d) == 0,
{
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
    /* code modified by LLM (iteration 2): Fixed lemma calls and added proper verification */
    proof {
        lemma_overlap_bounds(a as int, b as int, c as int, d as int);
        lemma_overlap_nonnegative(a as int, b as int, c as int, d as int);
        lemma_overlap_cases(a as int, b as int, c as int, d as int);
    }
    
    let max_ac = if a > c { a } else { c };
    let min_bd = if b < d { b } else { d };
    
    let overlap = if min_bd > max_ac { min_bd - max_ac } else { 0 };
    
    proof {
        assert(overlap as int == interval_overlap_length(a as int, b as int, c as int, d as int)) by {
            assert(valid_input(a as int, b as int, c as int, d as int));
        }
    }
    
    assert(0 <= overlap && overlap <= 100);
    overlap
}
// </vc-code>


}

fn main() {}