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
fn min_five_exec(a: i8, b: i8, c: i8, d: i8, e: i8) -> (m: i8)
    requires
        a >= 1,
        b >= 1,
        c >= 1,
        d >= 1,
        e >= 1,
    ensures
        m as int == min_capacity(a as int, b as int, c as int, d as int, e as int)
{
    let temp1 = if a <= b { a } else { b };
    let temp2 = if temp1 <= c { temp1 } else { c };
    let temp3 = if temp2 <= d { temp2 } else { d };
    let m = if temp3 <= e { temp3 } else { e };
    m
}

/* helper modified by LLM (iteration 4): [fixed compilation error by removing non-existent lemma] */
proof fn lemma_ceil_div_ge_1(a: int, b: int)
    requires
        a >= 1,
        b >= 1,
    ensures
        ceil_div(a, b) >= 1,
{
    assert(a + b - 1 >= b);
    assert(ceil_div(a, b) >= 1);
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
    /* code modified by LLM (iteration 4): [no change, fix was in helpers] */
    let min_cap_val = min_five_exec(a, b, c, d, e);

    // Use i16 for calculations to avoid potential overflow of i8
    let n_16 = n as i16;
    let min_cap_16 = min_cap_val as i16;
    
    let groups = (n_16 + min_cap_16 - 1) / min_cap_16;
    let result_16 = 4i16 + groups;

    proof {
        let n_int = n as int;
        let min_cap_int = min_cap_val as int;
        lemma_ceil_div_ge_1(n_int, min_cap_int);
        let groups_int = ceil_div(n_int, min_cap_int);
        assert(groups_int >= 1);
        let result_int = 4 + groups_int;
        assert(result_int >= 5);

        assert(n_16 as int + min_cap_16 as int - 1 == n_int + min_cap_int - 1);
        assert(groups as int == groups_int);
        assert(result_16 as int == result_int);
    }
    
    let result = result_16 as i8;
    result
}
// </vc-code>


}

fn main() {}