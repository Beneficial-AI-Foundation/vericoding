// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_poly_eval_at1(arr: Seq<int>, off: int, scl: int)
    requires
        arr.len() == 2,
        arr[0] == off,
        arr[1] == scl,
    ensures
        arr[0] + arr[1] == off + scl,
{
}

proof fn lemma_poly_eval_at1_i8(arr: Seq<i8>, off: i8, scl: i8)
    requires
        arr.len() == 2,
        arr[0] == off,
        arr[1] == scl,
    ensures
        arr[0] as int + arr[1] as int == off as int + scl as int,
{
    /* helper modified by LLM (iteration 2): Added i8 version to match types */
}
// </vc-helpers>

// <vc-spec>
fn polyline(off: i8, scl: i8) -> (result: [i8; 2])
    ensures
        /* Constant term is always off */
        result[0] == off,
        /* Linear coefficient is always scl */
        result[1] == scl,
        /* Size is always 2 (representing up to degree 1 polynomial) */
        result@.len() == 2,
        /* Example evaluation: if we evaluate at x=1, we get off + scl */
        result[0] as int + result[1] as int == off as int + scl as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Use i8 helper instead of int helper */
    let result = [off, scl];
    proof {
        lemma_poly_eval_at1_i8(result@, off, scl);
    }
    result
}
// </vc-code>


}
fn main() {}