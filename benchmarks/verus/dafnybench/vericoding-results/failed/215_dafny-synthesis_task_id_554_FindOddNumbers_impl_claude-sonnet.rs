use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)
    // All numbers in the output are odd and exist in the input 
    ensures forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr@.contains(odd_list[i])
    // All odd numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> odd_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    let mut odd_list = Vec::new();
    
    for i in 0..arr.len()
        invariant
            // All numbers in odd_list so far are odd and exist in arr
            forall|j: int| 0 <= j < odd_list.len() ==> is_odd(odd_list[j] as int) && arr@.contains(odd_list[j]),
            // All odd numbers we've seen so far are in odd_list
            forall|j: int| 0 <= j < i ==> (is_odd(arr[j] as int) ==> odd_list@.contains(arr[j])),
    {
        if arr[i] % 2 == 1 {
            proof {
                assert(is_odd(arr[i] as int));
            }
            odd_list.push(arr[i]);
        }
    }
    
    odd_list
}
// </vc-code>

fn main() {}

}