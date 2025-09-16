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
    /* code modified by LLM (iteration 5): Added lemmas to help prove filter properties */
    let mut positive_list = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            positive_list@ == input@.take(i as int).filter(|x: i32| x > 0),
        decreases input.len() - i
    {
        if input[i] > 0 {
            proof {
                let old_filtered = input@.take(i as int).filter(|x: i32| x > 0);
                let new_take = input@.take((i + 1) as int);
                assert(new_take == input@.take(i as int).push(input@[i as int]));
                let new_filtered = new_take.filter(|x: i32| x > 0);
                assert(input@[i as int] > 0);
                assert forall|j: int| 0 <= j < old_filtered.len() implies old_filtered[j] == positive_list@[j];
                assert(new_filtered.len() == old_filtered.len() + 1);
                assert(new_filtered == old_filtered.push(input@[i as int]));
            }
            positive_list.push(input[i]);
        } else {
            proof {
                let old_filtered = input@.take(i as int).filter(|x: i32| x > 0);
                let new_take = input@.take((i + 1) as int);
                assert(new_take == input@.take(i as int).push(input@[i as int]));
                let new_filtered = new_take.filter(|x: i32| x > 0);
                assert(!(input@[i as int] > 0));
                assert(new_filtered == old_filtered);
            }
        }
        i += 1;
    }
    assert(input@.take(input.len() as int) == input@);
    positive_list
}
// </vc-code>

}
fn main() {}