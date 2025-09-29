// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn calculate_deposit(initial: int, years: int) -> int
    decreases years
{
    if years <= 0 { 
        initial 
    } else { 
        let prev_deposit = calculate_deposit(initial, years - 1);
        prev_deposit + prev_deposit / 100
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lower bound on deposit growth */
proof fn calc_lower_bound(y: int)
    requires
        y >= 0,
    ensures
        calculate_deposit(100, y) >= 100 + y,
    decreases y
{
    if y == 0 {
        assert(calculate_deposit(100, 0) == 100);
    } else {
        calc_lower_bound(y - 1);
        let p = calculate_deposit(100, y - 1);
        assert(p >= 100 + (y - 1));
        assert(p >= 100);
        assert(y > 0);
        assert(calculate_deposit(100, y) == p + p / 100);
        assert(p / 100 >= 1);
        assert(p + p / 100 >= p + 1);
        assert(p + 1 >= 100 + y);
    }
}

/* helper modified by LLM (iteration 2): strict monotonicity of deposit */
proof fn calc_strict_incr(y: int)
    requires
        y >= 0,
    ensures
        calculate_deposit(100, y + 1) > calculate_deposit(100, y),
    decreases y
{
    let p = calculate_deposit(100, y);
    calc_lower_bound(y);
    assert(p >= 100);
    assert(y + 1 > 0);
    assert(calculate_deposit(100, y + 1) == p + p / 100);
    assert(p / 100 >= 1);
    assert(p + p / 100 >= p + 1);
    assert(p + 1 > p);
}

/* helper modified by LLM (iteration 2): exact linear behavior for first 100 years */
proof fn exact_linear_upto_100(y: int)
    requires
        0 <= y,
        y <= 100,
    ensures
        calculate_deposit(100, y) == 100 + y,
    decreases y
{
    if y == 0 {
        assert(calculate_deposit(100, 0) == 100);
    } else {
        exact_linear_upto_100(y - 1);
        let p = calculate_deposit(100, y - 1);
        assert(p == 100 + (y - 1));
        assert(0 <= y - 1);
        assert(y - 1 < 100);
        assert((100 + (y - 1)) / 100 == 1);
        assert(calculate_deposit(100, y) == p + p / 100);
        assert(p / 100 == 1);
        assert(calculate_deposit(100, y) == p + 1);
        assert(p + 1 == 100 + y);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (years: i8)
    requires x >= 101
    ensures 
        years >= 0 &&
        calculate_deposit(100, years as int) >= x as int &&
        (years == 0 || calculate_deposit(100, (years - 1) as int) < x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): choose minimal years as x - 100 and prove correctness using exact linear behavior up to 100 years */
    let years_out: i8 = x - 100;
    proof {
        let gx: int = x as int;
        let gy: int = years_out as int;
        assert(gx >= 101);
        assert(gx <= i8::MAX as int);
        assert(gy == gx - 100);
        assert(gy >= 1);
        assert(gy <= 100);
        exact_linear_upto_100(gy);
        assert(calculate_deposit(100, gy) == 100 + gy);
        assert(100 + gy == gx);
        let gy_prev: int = gy - 1;
        assert(gy_prev >= 0);
        assert(gy_prev <= 100);
        exact_linear_upto_100(gy_prev);
        assert(calculate_deposit(100, gy_prev) == 100 + gy_prev);
        assert(100 + gy_prev == gx - 1);
        assert(gx - 1 < gx);
    }
    years_out
}
// </vc-code>


}

fn main() {}