use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    let mut i: int = 0;
    while i < arr@.len()
        invariant
            0 <= i <= arr@.len(),
            forall |k: int| 0 <= k < result@.len() ==> #[trigger] is_odd(result@[k]) && #[trigger] arr@.contains(result@[k]),
            forall |j: int| 0 <= j < i && is_odd(#[trigger] arr@[j]) ==> #[trigger] result@.contains(arr@[j])
    {
        if arr[i as usize] % 2 != 0 {
            proof {
                assert(is_odd(arr@[i]));
                assert(arr@.contains(arr@[i]));
            }
            result.push(arr[i as usize]);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}

}