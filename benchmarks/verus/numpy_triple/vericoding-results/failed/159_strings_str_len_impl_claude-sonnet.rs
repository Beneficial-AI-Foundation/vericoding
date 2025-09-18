// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): use ghost variable for nat type */
    let mut result: Vec<nat> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> {
                &&& result[j] == a[j]@.len()
                &&& result[j] >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            }
    {
        let ghost len: nat = a[i]@.len();
        result.push(len);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}