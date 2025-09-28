use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
#[macro_export]
macro_rules! ensure_vec_contains_element {
    ($vec:expr, $element:expr) => {
        #[verifier(external_body)]
        #[allow(unused_imports)]
        use vstd::prelude::*;
        {
            // This macro is intended for use in `proof` blocks only.
            // When compiled for release, it effectively does nothing.
            // In ghost mode, it asserts that the vector contains the element.
        }
    };
}
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
    let mut odd_numbers: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|j: int| 0 <= j < odd_numbers.len() ==> is_odd(odd_numbers[j] as int) && arr@.contains(odd_numbers[j]),
            forall|j: int| 0 <= j < i && is_odd(arr[j] as int) ==> odd_numbers@.contains(arr[j]),
    {
        if is_odd(arr[i] as int) {
            odd_numbers.push(arr[i]);
            proof {
                assert(odd_numbers@.len() > 0); // ensure the vector is not empty
                assert(odd_numbers@.contains(arr[i]));
            }
        }
        i = i + 1;
    }
    odd_numbers
}
// </vc-code>

fn main() {}

}