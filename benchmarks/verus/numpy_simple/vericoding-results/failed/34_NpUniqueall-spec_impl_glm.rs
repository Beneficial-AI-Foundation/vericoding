// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing by using non-ghost vector indexing */
fn contains(v: &Vec<i8>, x: i8) -> (result: bool)
    ensures result == exists|i: int| 0 <= i < v@.len() && #[trigger] v@[i] == x,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v@.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != x,
        decreases (v@.len()) - i,
    {
        if v[i] == x {
            return true;
        }
        i = i + 1;
    }
    false
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
/* code modified by LLM (iteration 5): fixed indexing by using non-ghost vector indexing */
{
    let mut ret = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            ret.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == arr@[k],
            forall|k: int, j: int| 0 <= k < ret@.len() && 0 <= j < k ==> ret@[k] != ret@[j],
        decreases (arr@.len()) - i,
    {
        if !contains(&ret, arr[i]) {
            ret.push(arr[i]);
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}