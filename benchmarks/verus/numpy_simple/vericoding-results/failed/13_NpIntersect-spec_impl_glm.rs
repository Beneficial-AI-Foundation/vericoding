// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed bounds checking and loop invariants */
fn intersect_helper(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires
        a@.len() >= 0,
        b@.len() >= 0
    ensures
        result.len() <= a.len() && result.len() <= b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
{
    let mut result = Vec::new();
    let a_len = a.len();
    let b_len = b.len();
    let mut i = 0;
    let mut j = 0;
    
    while i < a_len && j < b_len
        invariant
            0 <= i <= a_len,
            0 <= j <= b_len,
            result.len() <= i && result.len() <= j,
            forall|i_idx: int, j_idx: int| 0 <= i_idx < i && 0 <= j_idx < j ==> (
                (a@[i_idx] == b@[j_idx] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i_idx]) &&
                (a@[i_idx] != b@[j_idx] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i_idx])
            )
        decreases (a_len - i) + (b_len - j)
    {
        if a[i] == b[j] {
            proof {
                assert(i < a_len && j < b_len);
            }
            result.push(a[i]);
            i = i + 1;
            j = j + 1;
        } else if a[i] < b[j] {
            i = i + 1;
        } else {
            j = j + 1;
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn intersect(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() < a.len() && result.len() < b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): calling the corrected helper function */
{
    intersect_helper(a, b)
}
// </vc-code>


}
fn main() {}