// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to loop */
fn vec_contains(v: &Vec<i32>, item: i32) -> (b: bool)
    ensures b == v@.contains(item)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            // The item is not in the prefix v[0..i]
            !v@.subrange(0, i as int).contains(item)
        decreases v.len() - i
    {
        if v[i] == item {
            return true;
        }
        i = i + 1;
    }
    return false;
}
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
    /* code modified by LLM (iteration 4): added decreases clause to loop */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            // All elements in `result` are from the processed part of `arr1` (arr1[0..i])
            // and are not present in `arr2`.
            forall|k: int| 0 <= k < result.len() ==> 
                (arr1@.subrange(0, i as int).contains(result@[k]) && !arr2@.contains(result@[k])),
            // All processed elements from `arr1` are accounted for: they are either
            // in `arr2` (and thus excluded) or in `result`.
            forall|k: int| 0 <= k < (i as int) ==> 
                (arr2@.contains(arr1@[k]) || result@.contains(arr1@[k])),
        decreases arr1.len() - i
    {
        let item = arr1[i];
        if !vec_contains(arr2, item) {
            result.push(item);
            proof {
                // Prove that the newly pushed item was not in arr2
                assert(!arr2@.contains(item));
                // Prove that the new result's items are all in arr1's prefix
                let new_result_seq = result@;
                assert(new_result_seq.last().unwrap() == item);
                assert(arr1@.subrange(0, (i+1) as int).contains(item));
                
                forall|k: int| 0 <= k < result.len() ==> 
                  (arr1@.subrange(0, (i+1) as int).contains(result@[k])) by {
                    assert(arr1@.subrange(0, i as int).contains(result@[k]));
                }

                forall|k: int| 0 <= k < (i+1) as int implies (arr2@.contains(arr1@[k]) || new_result_seq.contains(arr1@[k])) by {
                    if k < i {
                        assert(arr2@.contains(arr1@[k]) || result@.subst_add(result.len() as int, item).contains(arr1@[k]));
                    } else {
                        assert(k == i);
                        assert(arr1@[k] == item);
                        assert(new_result_seq.contains(item)); 
                   }
                }
            }
        } else {
             proof {
                assert(arr2@.contains(arr1@[i]));
             }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}