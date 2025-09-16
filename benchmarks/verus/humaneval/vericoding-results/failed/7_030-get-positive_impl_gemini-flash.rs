// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */

// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add invariant on positive_list.len() relationship with positive elements count */
{
    let mut positive_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < input.len()
        invariant
            0 <= i && i <= input.len(),
            positive_list@ == input@.take(i as int).filter(|x: i32| x > 0),
            positive_list.len() == input@.take(i as int).filter(|x: i32| x > 0).len(),
        decreases input.len() - i
    {
        let val: i32 = input[i];
        if val > 0 {
            positive_list.push(val);
        }
        i = i + 1;
    }
    positive_list
}
// </vc-code>

}
fn main() {}