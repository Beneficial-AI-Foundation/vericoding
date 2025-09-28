// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n
}

spec fn max_in_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    via max_in_seq_decreases
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail = s.subrange(1, s.len() as int);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max { s[0] } else { tail_max }
    }
}

#[via_fn]
proof fn max_in_seq_decreases(s: Seq<int>) {
    assume(false);
}

spec fn valid_result(n: int, heights: Seq<int>, result: int) -> bool
    recommends valid_input(n, heights)
{
    result == max_in_seq(heights) &&
    forall|i: int| 0 <= i < heights.len() ==> heights[i] <= result &&
    exists|i: int| 0 <= i < heights.len() && heights[i] == result
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix old() call in max_in_seq_props */
proof fn max_in_seq_props(heights: Seq<int>) 
    requires
        heights.len() > 0,
    ensures
        max_in_seq(heights) == old(max_in_seq(heights)),
        forall|i: int| 0 <= i < heights.len() ==> heights[i] <= max_in_seq(heights),
        exists|i: int| 0 <= i < heights.len() && heights[i] == max_in_seq(heights),
    decreases heights.len()
{
    if heights.len() == 1 {
        assert(heights[0] == max_in_seq(heights));
    } else {
        let tail = heights.subrange(1, heights.len() as int);
        proof {
            max_in_seq_props(tail);
        }
        if heights[0] >= max_in_seq(tail) {
            assert(heights[0] == max_in_seq(heights));
        } else {
            assert(max_in_seq(tail) == max_in_seq(heights));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, heights@.map(|i, x: i8| x as int))
    ensures valid_result(n as int, heights@.map(|i, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type issues and ensure proper conversion */
{
    proof {
        max_in_seq_props(heights@.map(|i, x: i8| x as int));
    }
    
    let n_usize = n as usize;
    let mut max_value = heights[0];
    let mut i = 1;
    
    while i < n_usize
        invariant
            i <= n_usize,
            forall|j: int| 0 <= j < i ==> (heights@[j as int] as int) <= (max_value as int),
            exists|j: int| 0 <= j < i && (heights@[j as int] as int) == (max_value as int),
        decreases n_usize - i
    {
        if heights[i] > max_value {
            max_value = heights[i];
        }
        i = i + 1;
    }
    
    max_value
}
// </vc-code>


}

fn main() {}