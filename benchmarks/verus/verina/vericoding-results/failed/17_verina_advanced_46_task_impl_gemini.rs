// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec functions for Kadane's algorithm */
spec fn max_ending_here_spec(s: Seq<i32>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let sub_s = s.subrange(0, s.len() - 1);
        let prev_max_ending = max_ending_here_spec(sub_s);
        let ending_here = prev_max_ending + s.last();
        if ending_here > 0 { ending_here } else { 0 }
    }
}

spec fn max_so_far_spec(s: Seq<i32>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let sub_s = s.subrange(0, s.len() - 1);
        let prev_max = max_so_far_spec(sub_s);
        let new_max_ending = max_ending_here_spec(s);
        if prev_max > new_max_ending { prev_max } else { new_max_ending }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(numbers: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented Kadane's algorithm with invariants */
    let mut max_so_far: i32 = 0;
    let mut max_ending_here: i32 = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            max_so_far >= 0,
            max_ending_here >= 0,
            max_ending_here as int == max_ending_here_spec(numbers@.subrange(0, i as int)),
            max_so_far as int == max_so_far_spec(numbers@.subrange(0, i as int)),
        decreases numbers.len() - i
    {
        let current_val = numbers[i];
        
        max_ending_here = max_ending_here + current_val;
        if max_ending_here < 0 {
            max_ending_here = 0;
        }

        if max_so_far < max_ending_here {
            max_so_far = max_ending_here;
        }

        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}