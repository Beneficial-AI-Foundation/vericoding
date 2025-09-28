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
    let mut negative_list: Vec<int> = Vec::new();
    let mut i: int = 0;

    while i < arr.len()
        invariant
            0 <= i,
            i <= arr.len(),
            // All numbers in negative_list so far are negative and come from arr
            forall|j: int| 0 <= j < negative_list.len() ==>
                is_negative(negative_list[j]) && (exists|k: int| 0 <= k < i && arr[k] == negative_list[j]),
            // All negative numbers in arr up to index i-1 are in negative_list
            forall|k: int| 0 <= k < i && is_negative(arr[k]) ==>
                (exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[k]),
    {
        // Prove that i is a valid index for arr
        // Since i < arr.len() from the loop condition and i is non-negative,
        // i can be safely cast to usize for indexing.
        assert(0 <= i && i < arr.len());
        let current_val = arr[i as usize]; 
        if is_negative(current_val) {
            negative_list.push(current_val);
        }
        i = i + 1;
    }
    negative_list
}
// </vc-code>

fn main() {}

}