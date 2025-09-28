use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>

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
    let mut negative_list = Vec::new();
    for i in 0..arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 
                #![trigger negative_list[k]]
                0 <= k < negative_list.len() ==>
                is_negative(negative_list[k]),
            forall|k: int| 
                #![trigger negative_list[k]]
                0 <= k < negative_list.len() ==>
                exists|j: int| 
                    #![trigger arr[j] == negative_list[k]]
                    0 <= j < i && arr[j] == negative_list[k],
            forall|j: int| 
                #![trigger arr[j]]
                0 <= j < i && is_negative(arr[j]) ==>
                exists|k: int| 
                    #![trigger negative_list[k] == arr[j]]
                    0 <= k < negative_list.len() && negative_list[k] == arr[j]
    {
        if arr[i] < 0 {
            negative_list.push(arr[i]);
        }
    }
    negative_list
}
// </vc-code>

fn main() {}

}