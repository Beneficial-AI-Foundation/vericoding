// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix filter_even spec function with proper syntax */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }

spec fn filter_even(s: Seq<u32>) -> Seq<u32> {
    s.filter(|x: u32| is_even(*x))
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix loop invariant with proper sequence subrange */
{
    let mut even_numbers = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            even_numbers@ == filter_even(arr@.subrange(0, i as int)),
            i <= arr.len(),
        decreases arr.len() - i
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