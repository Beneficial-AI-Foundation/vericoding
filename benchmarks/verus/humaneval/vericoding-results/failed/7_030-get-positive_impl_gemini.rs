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
    /* code modified by LLM (iteration 5): fixed compilation error by removing the proof block which called a non-existent function. */
    let mut positive_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            positive_list@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i
    {
        let elem = input[i];
        if elem > 0 {
            positive_list.push(elem);
        }
        i = i + 1;
    }
    positive_list
}
// </vc-code>

}
fn main() {}