// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix integer multiplication with explicit cast */
fn triple_internal(n: int) -> (r: int)
    ensures
        r == 3 * n,
{
    3 as int * n
}

proof fn triple_div_lemma(x: int, y: int)
    requires
        y != 0,
    ensures
        (x * y) / y == x,
{
}

spec fn to_int(n: i32) -> int { n as int }
spec fn to_i32(n: int) -> i32 { n as i32 }
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Maintain same implementation with proper type handling */
{
    let ghost x_int = to_int(x);
    let ghost result_int = triple_internal(x_int);
    proof {
        triple_div_lemma(x_int, 3);
    }
    let result: i32 = to_i32(result_int);
    result
}
// </vc-code>

}
fn main() {}