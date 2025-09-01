use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helper lemmas needed for this implementation
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let mut positive_list: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < input.len()
        invariant i <= input.len();
        invariant positive_list@ == input@[0..i].filter(|x: i32| x > 0);
        decreases input.len() - i;
    {
        match input.get(i) {
            Some(v) => {
                let val: i32 = *v;
                if val > 0 {
                    positive_list.push(val);
                }
            }
            None => {}
        }
        i = i + 1;
    }
    positive_list
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}