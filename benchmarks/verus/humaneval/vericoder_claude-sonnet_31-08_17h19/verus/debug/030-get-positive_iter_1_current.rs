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
    let mut positive_list = Vec::new();
    
    for i in 0..input.len()
        invariant
            positive_list@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            positive_list.push(input[i]);
        }
    }
    
    positive_list
}
// </vc-code>

fn main() {}
}