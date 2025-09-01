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
    let mut result = Vec::new();
    let mut i: int = 0;
    let n: int = input.len() as int;
    while i < n
        invariant
            0 <= i <= n,
            result@ == input@.take(i).filter(|x: i32| x > 0),
        decreases n - i,
    {
        let x = input[i as usize];
        if x > 0 {
            result.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}