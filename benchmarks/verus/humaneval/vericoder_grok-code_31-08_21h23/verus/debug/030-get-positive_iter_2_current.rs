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
    proof {
        let tracked mut ti: int = 0;
    }
    while i < input.len()
        invariant
            ti == i as int,
            result@ == input@.subrange(0, ti).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            result.push(input[i]);
        }
        i += 1;
        proof {
            ti = ti + 1;
        }
    }
    result
}
// </vc-code>

fn main() {}
}