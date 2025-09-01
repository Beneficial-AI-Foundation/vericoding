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
    let mut i = 0;
    while i < input.len()
        invariant
            forall |j: int| 0 <= j < i && input@[j] > 0 ==> exists |k: int| 0 <= k < positive_list.len() && positive_list@[k] == input@[j],
            forall |j: int| 0 <= j < positive_list.len() ==> exists |k: int| 0 <= k < i && input@[k] == positive_list@[j] && input@[k] > 0,
            input@.len() == input.len(),
            positive_list@.len() == positive_list.len(),
    {
        if input[i] > 0 {
            positive_list.push(input[i]);
        }
        i = i + 1;
    }
    assert(positive_list@ == input@.filter(|x: i32| x > 0));
    positive_list
}
// </vc-code>

fn main() {}
}