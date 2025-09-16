// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to the while loop and fixed casting in invariant for take method to use usize. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i as nat <= input@.len(),
            result@ == input@.take(i as usize).filter(|x: i32| x > 0),
        decreases input@.len() - i as int
    {
        if input[i] > 0 {
            result.push(input[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}