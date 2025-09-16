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
    /* code modified by LLM (iteration 5): fixed type error by casting i to int for indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i
    {
        if input[i as int] > 0 {
            result.push(input[i as int]);
        }
        proof {
            let old_i = i as int;
            let new_i = (i + 1) as int;
            assert(input@.subrange(0, new_i) == input@.subrange(0, old_i).push(input@[old_i]));
            if input[i as int] > 0 {
                assert(input@.subrange(0, new_i).filter(|x: i32| x > 0) == 
                       input@.subrange(0, old_i).filter(|x: i32| x > 0).push(input@[old_i]));
            } else {
                assert(input@.subrange(0, new_i).filter(|x: i32| x > 0) == 
                       input@.subrange(0, old_i).filter(|x: i32| x > 0));
            }
        }
        i += 1;
    }
    proof {
        assert(i == input.len());
        assert(input@.subrange(0, i as int) == input@);
    }
    result
}
// </vc-code>

}
fn main() {}