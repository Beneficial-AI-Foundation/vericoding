// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed as verification errors are in code section */
fn is_in(vec: &Vec<i8>, elem: i8) -> (ret: bool)
    ensures
        ret <==> exists|i: int| 0 <= i < vec@.len() && #[trigger] vec@[i] == elem,
{
    let mut j = 0;
    while j < vec.len()
        invariant
            0 <= j <= vec.len(),
            !exists|k: int| 0 <= k < j && vec@[k] == elem,
        decreases vec.len() - j
    {
        if vec[j] == elem {
            return true;
        }
        j += 1;
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
{
    /* code modified by LLM (iteration 5): Added proof assertions to maintain and extend loop invariant */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@.len() <= i,
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> result@[j] != result@[k],
            forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < result@.len() && result@[k] == #[trigger] arr@[j],
        decreases arr.len() - i
    {
        let elem = arr[i];
        if !is_in(&result, elem) {
            result.push(elem);
            proof {
                assert(forall|k: int| 0 <= k < result@.len() - 1 ==> result@[k] != elem);
            }
        }
        proof {
            assert(exists|k: int| 0 <= k < result@.len() && result@[k] == arr@[i]);
        }
        i += 1;
    }
    proof {
        // loop invariant at end ensures the postconditions
    }
    result
}
// </vc-code>


}
fn main() {}