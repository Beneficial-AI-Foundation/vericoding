// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed index to usize and adjusted invariant to use int conversions */
    let mut even_numbers = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            even_numbers@ == arr@.take(i as int).filter(|x: u32| x % 2 == 0)
        decreases (arr.len() as int) - (i as int)
    {
        if arr[i] % 2 == 0 {
            even_numbers.push(arr[i]);
        }
        i += 1;
    }
    even_numbers
}
// </vc-code>

}
fn main() {}