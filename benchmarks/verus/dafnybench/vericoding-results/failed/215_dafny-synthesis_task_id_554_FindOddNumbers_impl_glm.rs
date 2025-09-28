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
    let mut odd_list: Vec<i32> = Vec::new();
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < odd_list.len() ==> is_odd(odd_list[k] as int) && {
                #[trigger]
                arr@.contains(odd_list[k])
            },
            forall|k: int| 0 <= k < i && is_odd(arr[k] as int) ==> {
                #[trigger]
                odd_list@.contains(arr[k])
            }
    {
        let val = arr[i as int];
        if is_odd(val as int) {
            odd_list.push(val);
        }
    }
    odd_list
}
// </vc-code>

fn main() {}

}