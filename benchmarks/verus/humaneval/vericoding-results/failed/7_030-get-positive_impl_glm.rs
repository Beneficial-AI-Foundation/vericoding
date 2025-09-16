// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed missing closing paren */
spec fn is_positive(x: i32) -> bool {
    x > 0
}

/* helper modified by LLM (iteration 3): fixed syntax error in condition expression */
proof fn filtered_prefix_step(s: Seq<i32>, j: nat)
    requires
        j < s.len(),
    ensures
        s.subrange(0, j+1).filter(|x| is_positive(x)) == 
            if is_positive(s[j]) {
                s.subrange(0, j).filter(|x| is_positive(x)).push(s[j])
            } else {
                s.subrange(0, j).filter(|x| is_positive(x))
            }
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected loop implementation */
{
    let mut positive_list = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            positive_list@ == input@.subrange(0, i).filter(|x| is_positive(x)),
            0 <= i <= input.len(),
        decreases input.len() - i
    {
        if is_positive(input[i]) {
            positive_list.push(input[i]);
        }
        proof {
            filtered_prefix_step(input@, i);
        }
        i += 1;
    }
    positive_list
}
// </vc-code>

}
fn main() {}