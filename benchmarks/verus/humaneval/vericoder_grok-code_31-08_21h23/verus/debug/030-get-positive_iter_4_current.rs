use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            result.push(input[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}