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
    let mut result = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i
    {
        let x = input[i];
        if x > 0 {
            result.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}