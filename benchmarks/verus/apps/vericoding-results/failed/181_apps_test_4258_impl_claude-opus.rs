// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, t: int) -> bool {
    1 <= a <= 20 && 1 <= b <= 20 && 1 <= t <= 20
}

spec fn production_count(a: int, t: int) -> int {
    if a > 0 { t / a } else { 0 }
}

spec fn total_biscuits(a: int, b: int, t: int) -> int {
    if a > 0 { b * production_count(a, t) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed bounds proof and added helper for safe multiplication */
proof fn lemma_production_bounds(a: int, b: int, t: int)
    requires valid_input(a, b, t)
    ensures
        0 <= production_count(a, t) <= 20,
        0 <= total_biscuits(a, b, t) <= 400,
        total_biscuits(a, b, t) == b * production_count(a, t)
{
    assert(a > 0);
    assert(production_count(a, t) == t / a);
    assert(t <= 20);
    assert(a >= 1);
    assert(t / a <= t / 1);
    assert(t / 1 == t);
    assert(production_count(a, t) <= 20);
    assert(production_count(a, t) >= 0);
    assert(total_biscuits(a, b, t) == b * production_count(a, t));
    assert(b <= 20);
    assert(production_count(a, t) <= 20);
    assert(b * production_count(a, t) <= 20 * 20);
    assert(total_biscuits(a, b, t) <= 400);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, t: i8) -> (result: i8)
    requires valid_input(a as int, b as int, t as int)
    ensures result as int == total_biscuits(a as int, b as int, t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i16 for intermediate computation to avoid overflow */
    let production_runs = (t / a) as i16;
    
    proof {
        lemma_production_bounds(a as int, b as int, t as int);
        assert(a as int > 0);
        assert(production_runs as int == (t as int) / (a as int));
        assert(production_runs as int == production_count(a as int, t as int));
        assert(production_runs as int <= 20);
    }
    
    let b_wide = b as i16;
    let result_wide = b_wide * production_runs;
    
    proof {
        assert(result_wide as int == (b as int) * production_runs as int);
        assert(production_runs as int == production_count(a as int, t as int));
        assert(result_wide as int == (b as int) * production_count(a as int, t as int));
        assert(result_wide as int == total_biscuits(a as int, b as int, t as int));
        lemma_production_bounds(a as int, b as int, t as int);
        assert(total_biscuits(a as int, b as int, t as int) <= 400);
        assert(result_wide as int <= 400);
        assert(result_wide <= 400i16);
    }
    
    result_wide as i8
}
// </vc-code>


}

fn main() {}