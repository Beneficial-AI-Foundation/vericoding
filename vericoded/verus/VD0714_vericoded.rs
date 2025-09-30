use vstd::prelude::*;

verus! {

/**
 * Remove odd numbers from an array of numbers
 **/

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// Helper lemma to maintain the invariant that all elements in result are even and from arr
proof fn even_list_properties(arr: &[i32], result: &Vec<i32>, j: int)
    requires
        0 <= j <= arr.len(),
        forall|k: int| 0 <= k < result.len() ==> is_even(result[k] as int) && arr@.contains(result[k]),
        forall|k: int| 0 <= k < j && is_even(arr@[k] as int) ==> result@.contains(arr@[k]),
    ensures
        forall|k: int| 0 <= k < result.len() ==> is_even(result[k] as int) && arr@.contains(result[k]),
        forall|k: int| 0 <= k < j && is_even(arr@[k] as int) ==> result@.contains(arr@[k]),
{
}
// </vc-helpers>

// <vc-spec>
fn remove_odd_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    ensures
        // All numbers in the output are even and exist in the input 
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && arr@.contains(even_list[i]),
        // All even numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> even_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All elements in result are even and from arr
            forall|k: int| 0 <= k < result.len() ==> is_even(result[k] as int) && arr@.contains(result[k]),
            // All even elements we've seen so far are in result
            forall|k: int| 0 <= k < i && is_even(arr@[k] as int) ==> result@.contains(arr@[k]),
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            let ghost old_result_view = result@;
            result.push(arr[i]);
            
            proof {
                // Prove that the new element maintains our invariants
                assert(is_even(arr@[i as int] as int));
                assert(result@.len() == old_result_view.len() + 1);
                assert(result@[result@.len() - 1] == arr@[i as int]);
                
                // All previous elements are still there
                assert forall|k: int| 0 <= k < old_result_view.len() implies result@[k] == old_result_view[k] by {
                    assert(result@.take(old_result_view.len() as int) =~= old_result_view);
                }
                
                // The new element is in result
                assert(result@.contains(arr@[i as int]));
                
                // All even elements up to i are now in result
                assert forall|k: int| 0 <= k <= i && is_even(arr@[k] as int) implies result@.contains(arr@[k]) by {
                    if k < i {
                        assert(old_result_view.contains(arr@[k]));
                        assert(result@.contains(arr@[k]));
                    } else {
                        assert(k == i as int);
                        assert(result@.contains(arr@[i as int]));
                    }
                }
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}