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
proof fn lemma_ceil_div_positive(n: i8, d: i8) -> (q: i8)
    requires n >= 0 && d >= 1
    ensures q as int == ceil_div(n as int, d as int)
{
    let q_int = ceil_div(n as int, d as int);
    assert(q_int >= 0);
    assert(q_int <= (n as int + d as int - 1) / d as int);
    q_int as i8
}/* helper modified by LLM (iteration 5): Remove ghost code from exec context */

proof fn lemma_min_capacity_properties(a: i8, b: i8, c: i8, d: i8, e: i8) 
    requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
    ensures min_capacity(a as int, b as int, c as int, d as int, e as int) <= a as int &&
            min_capacity(a as int, b as int, c as int, d as int, e as int) <= b as int &&
            min_capacity(a as int, b as int, c as int, d as int, e as int) <= c as int &&
            min_capacity(a as int, b as int, c as int, d as int, e as int) <= d as int &&
            min_capacity(a as int, b as int, c as int, d as int, e as int) <= e as int
{
}

proof fn lemma_ceil_div_monotonic(n1: i8, n2: i8, d: i8)
    requires n1 <= n2 && d >= 1
    ensures ceil_div(n1 as int, d as int) <= ceil_div(n2 as int, d as int)
{
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
    /* code modified by LLM (iteration 5): Remove ghost code from exec context */
    proof {
        lemma_min_capacity_properties(a, b, c, d, e);
    }
    
    let min_val = if a <= b { a } else { b };
    let min_val = if min_val <= c { min_val } else { c };
    let min_val = if min_val <= d { min_val } else { d };
    let min_val = if min_val <= e { min_val } else { e };
    
    let n_int = n as i32;
    let min_val_int = min_val as i32;
    
    let groups_int = (n_int + min_val_int - 1) / min_val_int;
    let groups = groups_int as i8;
    
    proof {
        let ceil_result = lemma_ceil_div_positive(n, min_val);
        assert(ceil_result as int == ceil_div(n as int, min_val as int));
        assert(ceil_result == groups);
    }
    
    let result = 4 + groups;
    
    result
}
// </vc-code>


}

fn main() {}