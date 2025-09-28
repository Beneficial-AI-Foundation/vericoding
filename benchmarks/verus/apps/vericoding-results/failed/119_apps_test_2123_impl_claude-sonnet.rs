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
/* helper modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
proof fn max_in_seq_exists(s: Seq<int>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && s[i] == max_in_seq(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == max_in_seq(s));
    } else {
        let tail = s.subrange(1, s.len() as int);
        max_in_seq_exists(tail);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max {
            assert(s[0] == max_in_seq(s));
        } else {
            assert(tail_max == max_in_seq(s));
            let witness_i: int = choose|i: int| 1 <= i < s.len() && s[i] == tail_max;
            assert(s[witness_i] == max_in_seq(s));
        }
    }
}

proof fn max_in_seq_bounds(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| #[trigger] s[i] 0 <= i < s.len() ==> s[i] <= max_in_seq(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] <= max_in_seq(s));
    } else {
        let tail = s.subrange(1, s.len() as int);
        max_in_seq_bounds(tail);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max {
            assert(forall|i: int| #[trigger] s[i] 0 <= i < s.len() ==> s[i] <= s[0]);
        } else {
            assert(forall|i: int| #[trigger] s[i] 0 <= i < s.len() ==> s[i] <= tail_max);
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
{
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
    let mut max_val = heights[0];
    let mut i = 1;
    
    while i < heights.len()
        invariant
            0 < i <= heights.len(),
            forall|j: int| #[trigger] heights@[j] 0 <= j < i ==> heights@[j] <= max_val as int,
            exists|j: int| 0 <= j < i && heights@[j] == max_val as int
        decreases heights.len() - i
    {
        if heights[i] > max_val {
            max_val = heights[i];
        }
        i = i + 1;
    }
    
    proof {
        let heights_int = heights@.map(|i, x: i8| x as int);
        max_in_seq_exists(heights_int);
        max_in_seq_bounds(heights_int);
        
        assert(forall|j: int| #[trigger] heights_int[j] 0 <= j < heights.len() ==> heights_int[j] <= max_val as int);
        assert(exists|j: int| 0 <= j < heights.len() && heights_int[j] == max_val as int);
    }
    
    max_val
}
// </vc-code>


}

fn main() {}