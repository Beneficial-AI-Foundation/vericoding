use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// Auxiliary code and proofs can be added here if needed for verification
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr@.len(),
            forall|j: int| #[trigger] (0 <= j < result@.len()) ==> is_odd(result@[j] as int) && #[trigger] arr@.contains(result@[j]),
            forall|j: int| #[trigger] (0 <= j < i && is_odd(arr@[j] as int)) ==> #[trigger] result@.contains(arr@[j]),
    {
        if is_odd(arr[i] as int) {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}

}