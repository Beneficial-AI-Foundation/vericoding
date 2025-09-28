// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int, b: int, c: int, d: int, e: int) -> bool {
    n >= 1 && a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
}

spec fn min_capacity(a: int, b: int, c: int, d: int, e: int) -> int
    recommends a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
{
    let temp1 = if a <= b { a } else { b };
    let temp2 = if temp1 <= c { temp1 } else { c };
    let temp3 = if temp2 <= d { temp2 } else { d };
    if temp3 <= e { temp3 } else { e }
}

spec fn ceil_div(a: int, b: int) -> int
    recommends a >= 0 && b >= 1
{
    (a + b - 1) / b
}

spec fn correct_result(n: int, a: int, b: int, c: int, d: int, e: int, result: int) -> bool
    recommends valid_input(n, a, b, c, d, e)
{
    let min_cap = min_capacity(a, b, c, d, e);
    let groups = ceil_div(n, min_cap);
    result == 4 + groups
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min capacity for i8 inputs returning int */
spec fn min_capacity_i8(a: i8, b: i8, c: i8, d: i8, e: i8) -> int
    recommends (a as int) >= 1 && (b as int) >= 1 && (c as int) >= 1 && (d as int) >= 1 && (e as int) >= 1
{
    let t1: int = if (a as int) <= (b as int) { a as int } else { b as int };
    let t2: int = if t1 <= (c as int) { t1 } else { c as int };
    let t3: int = if t2 <= (d as int) { t2 } else { d as int };
    if t3 <= (e as int) { t3 } else { e as int }
}

/* helper modified by LLM (iteration 5): ceil div over ints */
spec fn ceil_div_from_int(n: int, cap: int) -> int
    recommends n >= 0 && cap >= 1
{
    (n + cap - 1) / cap
}

/* helper modified by LLM (iteration 5): lemma linking min_capacity_i8 to spec min_capacity */
proof fn lemma_min_capacity_i8_matches(a: i8, b: i8, c: i8, d: i8, e: i8)
    requires (a as int) >= 1 && (b as int) >= 1 && (c as int) >= 1 && (d as int) >= 1 && (e as int) >= 1
    ensures min_capacity_i8(a, b, c, d, e) == min_capacity(a as int, b as int, c as int, d as int, e as int)
{
    // by unfolding definitions the two expressions are identical
    assert(min_capacity_i8(a, b, c, d, e) == min_capacity(a as int, b as int, c as int, d as int, e as int));
}

/* helper modified by LLM (iteration 5): lemma linking ceil_div_from_int to spec ceil_div */
proof fn lemma_ceil_div_from_int_matches(n: int, cap: int)
    requires n >= 0 && cap >= 1
    ensures ceil_div_from_int(n, cap) == ceil_div(n, cap)
{
    assert(ceil_div_from_int(n, cap) == ceil_div(n, cap));
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, d: i8, e: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int, d as int, e as int)
    ensures 
        correct_result(n as int, a as int, b as int, c as int, d as int, e as int, result as int) &&
        result >= 5
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using int arithmetic to avoid i8 overflow in intermediate ops */
    let mincap_rt: i8 = {
        let t1 = if a <= b { a } else { b };
        let t2 = if t1 <= c { t1 } else { c };
        let t3 = if t2 <= d { t2 } else { d };
        if t3 <= e { t3 } else { e }
    };

    let mincap_i: int = mincap_rt as int;
    let n_i: int = n as int;

    let num: int = n_i + (mincap_i - 1);
    let groups_i: int = num / mincap_i;
    let result_i: int = 4 + groups_i;

    proof {
        // mincap is at least 1 because inputs are >= 1
        assert(mincap_i >= 1);
        // num is non-negative (since n_i >= 1 and mincap_i >= 1)
        assert(num >= 0);

        // Relate spec and runtime min capacity
        let mincap_spec: int = min_capacity_i8(a, b, c, d, e);
        lemma_min_capacity_i8_matches(a, b, c, d, e);
        assert(mincap_spec == min_capacity(a as int, b as int, c as int, d as int, e as int));
        assert(mincap_spec == mincap_i);

        // Relate groups to spec ceil_div
        let groups_spec: int = ceil_div_from_int(n_i, mincap_spec);
        lemma_ceil_div_from_int_matches(n_i, mincap_spec);
        assert(groups_spec == ceil_div(n_i, mincap_spec));
        assert(groups_spec == groups_i);

        // result matches spec
        let result_spec: int = 4 + groups_spec;
        assert(result_spec == result_i);
        assert(correct_result(n_i, a as int, b as int, c as int, d as int, e as int, result_spec));

        // ensure postcondition result >= 5
        assert(result_i >= 5);
    }

    result_i as i8
}

// </vc-code>


}

fn main() {}