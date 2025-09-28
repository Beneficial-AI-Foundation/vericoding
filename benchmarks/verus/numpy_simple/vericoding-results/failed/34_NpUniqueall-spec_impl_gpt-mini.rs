// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): membership check using nat indices */
fn vec_contains(v: &Vec<i8>, x: i8) -> bool {
    exists |i: nat| i < v@.len() && v@[i] == x
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using nat indices and maintain invariants */
    let mut ret: Vec<i8> = Vec::new();
    let mut i: nat = 0;
    while i < arr@.len()
        invariant
            i <= arr@.len(),
            ret@.len() <= arr@.len(),
            forall|p: nat, q: nat| p < ret@.len() && q < p ==> ret@[p] != ret@[q],
            forall|k: nat| k < i ==> exists|j: nat| j < ret@.len() && ret@[j] == arr@[k],
        decreases arr@.len() - i
    {
        let x: i8 = arr@[i];
        if !vec_contains(&ret, x) {
            ret.push(x);
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}