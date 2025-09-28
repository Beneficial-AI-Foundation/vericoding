use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
// Helper lemma to establish that elements added to the result maintain the invariant
proof fn lemma_push_maintains_invariant(arr: &[int], result: &Vec<int>, val: int, idx: int)
    requires
        0 <= idx < arr.len(),
        arr[idx as int] == val,
        is_negative(val),
        forall|i: int| 0 <= i < result.len() ==> 
            is_negative(result[i]) && exists|j: int| 0 <= j < arr.len() && arr[j as int] == result[i],
    ensures
        forall|i: int| 0 <= i < result.len() + 1 ==> {
            let new_result = result@.push(val);
            is_negative(new_result[i]) && exists|j: int| 0 <= j < arr.len() && arr[j as int] == new_result[i]
        }
{
    let new_result = result@.push(val);
    assert forall|i: int| 0 <= i < result.len() implies 
        is_negative(new_result[i]) && exists|j: int| 0 <= j < arr.len() && arr[j as int] == new_result[i]
    by {
        assert(new_result[i] == result[i]);
    }
    assert(new_result[result.len() as int] == val);
    assert(is_negative(val));
    assert(exists|j: int| 0 <= j < arr.len() && arr[j as int] == val);
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures
        // All numbers in the output are negative and exist in the input
        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],
        // All negative numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
// </vc-spec>
// <vc-code>
{
    let mut negative_list: Vec<int> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All numbers in negative_list are negative and from arr
            forall|k: int| 0 <= k < negative_list.len() ==> 
                is_negative(#[trigger] negative_list[k]) && 
                exists|j: int| 0 <= j < arr.len() && arr[j as int] == negative_list[k],
            // All negative numbers from arr[0..i] are in negative_list
            forall|k: int| 0 <= k < i && is_negative(#[trigger] arr[k as int]) ==> 
                exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[k as int],
    {
        if arr[i] < 0 {
            let old_len = negative_list.len();
            negative_list.push(arr[i]);
            
            proof {
                assert(is_negative(arr[i as int]));
                assert(forall|k: int| 0 <= k < old_len ==> 
                    is_negative(negative_list@[k]) && 
                    exists|j: int| 0 <= j < arr.len() && arr[j as int] == negative_list@[k]);
                assert(negative_list@[old_len as int] == arr[i as int]);
                assert(exists|j: int| 0 <= j < arr.len() && arr[j as int] == arr[i as int]) by {
                    assert(arr[i as int] == arr[i as int]);
                }
            }
        }
        i = i + 1;
    }
    
    negative_list
}
// </vc-code>

fn main() {}

}