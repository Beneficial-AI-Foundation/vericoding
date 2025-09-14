// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec wrapper for Vec contains using spec view */
spec fn elem_in_vec(v: &Vec<i32>, x: i32) -> bool { v@.contains(x) }
// </vc-helpers>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): ensure invariants preserved and use push-view facts */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            forall|j: int| 0 <= j && j < result@.len() ==> (arr1@.contains(result@[j]) && !arr2@.contains(result@[j])),
            forall|j: int| 0 <= j && j < i as int ==> (arr2@.contains(arr1@[j]) || result@.contains(arr1@[j])),
        decreases arr1.len() - i
    {
        let x = arr1[i];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < arr2.len()
            invariant
                j <= arr2.len(),
                found == (exists|k: int| 0 <= k && k < j as int && arr2@[k] == x),
            decreases arr2.len() - j
        {
            if arr2[j] == x {
                found = true;
            }
            j += 1;
        }
        proof {
            assert(found == arr2@.contains(x));
        }
        if !found {
            let old_len = result.len();
            result.push(x);
            proof {
                // push updates the spec view: new len = old_len + 1 and element at old_len is x
                assert(result@.len() == old_len as int + 1);
                assert(result@[old_len as int] == x);
                assert(result@.contains(x));
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}