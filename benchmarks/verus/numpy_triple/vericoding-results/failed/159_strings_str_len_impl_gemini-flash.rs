// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary comment */
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): remove `as nat` from ghost variable assignment */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            i >= 0,
            i <= a.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> {
                &&& result[j] == a[j]@.len()
                &&& result[j] >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            }
    {
        let s_len: nat = a[i]@.len();
        result.push(s_len);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}