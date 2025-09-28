use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
proof fn lemma_negative_preserved(arr: &[int], negative_list: &Vec<int>, old_len: nat, new_val: int)
    requires
        forall|i: int| 0 <= i < old_len ==> 
            is_negative(negative_list@[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list@[i],
        exists|k: int| 0 <= k < arr.len() && arr[k] == new_val,
        is_negative(new_val),
        negative_list.len() == old_len + 1,
        negative_list@[old_len as int] == new_val
    ensures
        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list@[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list@[i]
{
}

proof fn lemma_all_negatives_found(arr: &[int], negative_list: &Vec<int>, processed: nat)
    requires
        processed <= arr.len(),
        forall|i: int| 0 <= i < processed && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list@[j] == arr[i],
        forall|i: int| 0 <= i < negative_list.len() ==> 
            exists|j: int| 0 <= j < processed && arr[j] == negative_list@[i]
    ensures
        forall|i: int| 0 <= i < processed && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list@[j] == arr[i]
{
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
    let mut negative_list = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < negative_list.len() ==> 
                is_negative(negative_list@[k]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list@[k],
            forall|k: int| 0 <= k < i && is_negative(arr[k]) ==> 
                exists|j: int| 0 <= j < negative_list.len() && negative_list@[j] == arr[k],
    {
        if is_negative(arr[i]) {
            let ghost old_len = negative_list.len();
            negative_list.push(arr[i]);
            
            proof {
                lemma_negative_preserved(&arr, &negative_list, old_len as nat, arr[i]);
            }
        }
        i += 1;
    }
    
    proof {
        lemma_all_negatives_found(&arr, &negative_list, arr.len() as nat);
    }
    
    negative_list
}
// </vc-code>

fn main() {}

}