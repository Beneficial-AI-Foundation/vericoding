use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
// No helpers required for this proof.
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
    let mut negative_list = Vec::<int>::new();
    let mut i: int = 0;
    while i < arr.len() as int
        invariant 0 <= i && i <= arr.len() as int
        invariant forall|k: int| 0 <= k && k < negative_list.len() as int ==>
            is_negative(negative_list[k as usize]) && exists|j: int| 0 <= j && j < i && arr[j as usize] == negative_list[k as usize]
        invariant forall|j: int| 0 <= j && j < i && is_negative(arr[j as usize]) ==>
            exists|k: int| 0 <= k && k < negative_list.len() as int && negative_list[k as usize] == arr[j as usize]
    {
        let ai: int = arr[i as usize];
        if is_negative(ai) {
            let old_len = negative_list.len();
            negative_list.push(ai);
            proof {
                // After pushing, all previous elements still satisfy the first invariant
                // and the new element (at index old_len) is negative and comes from arr at index i.
                assert(old_len as int + 1 == negative_list.len() as int);
            }
        } else {
            // nothing to push; invariants for i+1 follow from invariants for i
        }
        i += 1;
    }
    negative_list
}
// </vc-code>

fn main() {}

}