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
    /* code modified by LLM (iteration 5): added decreases clause to while loop for termination */
    let mut even_numbers: Vec<u32> = Vec::new();
    let len = arr.len();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            even_numbers@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases len - i,
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