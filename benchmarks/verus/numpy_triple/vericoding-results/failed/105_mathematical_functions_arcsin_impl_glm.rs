// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -2 <= result[i] as int && result[i] as int <= 2 &&
            (x[i] as int == 0 ==> result[i] as int == 0) &&
            (x[i] as int == 1 ==> result[i] as int == 2) &&
            (x[i] as int == -1 ==> result[i] as int == -2)
        },
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x[i] as int <= x[j] as int ==> result[i] as int <= result[j] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariant and precondition issues */
    let len = x.len();
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < len
        invariant
            i <= len,
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> {
                -2 <= result[j] as int && result[j] as int <= 2 &&
                (x[j] as int == 0 ==> result[j] as int == 0) &&
                (x[j] as int == 1 ==> result[j] as int == 2) &&
                (x[j] as int == -1 ==> result[j] as int == -2)
            },
            forall|j: int, k: int| 0 <= j < i as int && 0 <= k < i as int && x[j] as int <= x[k] as int ==> result[j] as int <= result[k] as int,
        decreases (len - i) as nat
    {
        let val = x[i];
        let res_val = 2 * val;
        result.push(res_val);
        proof {
            assert(x[i] as int >= -1 && x[i] as int <= 1);
            assert(res_val as int >= -2 && res_val as int <= 2);
            if x[i] as int == 0 {
                assert(res_val as int == 0);
            }
            if x[i] as int == 1 {
                assert(res_val as int == 2);
            }
            if x[i] as int == -1 {
                assert(res_val as int == -2);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}