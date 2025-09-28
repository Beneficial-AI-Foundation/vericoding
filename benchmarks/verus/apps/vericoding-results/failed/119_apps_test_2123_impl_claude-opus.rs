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
proof fn max_in_seq_properties(s: Seq<int>)
    requires s.len() > 0
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[i] <= max_in_seq(s),
        exists|i: int| 0 <= i < s.len() && s[i] == max_in_seq(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] <= max_in_seq(s));
        assert(s[0] == max_in_seq(s));
    } else {
        let tail = s.subrange(1, s.len() as int);
        max_in_seq_properties(tail);
        
        assert forall|i: int| 1 <= i < s.len() implies s[i] <= max_in_seq(s) by {
            assert(tail[i - 1] == s[i]);
            assert(tail[i - 1] <= max_in_seq(tail));
            if s[0] >= max_in_seq(tail) {
                assert(max_in_seq(s) == s[0]);
                assert(s[i] <= max_in_seq(tail) <= s[0]);
            } else {
                assert(max_in_seq(s) == max_in_seq(tail));
            }
        }
        
        if s[0] >= max_in_seq(tail) {
            assert(s[0] == max_in_seq(s));
        } else {
            assert(exists|j: int| 1 <= j < s.len() && tail[j - 1] == max_in_seq(tail));
            assert(exists|j: int| 0 <= j < s.len() && s[j] == max_in_seq(s));
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
    /* code modified by LLM (iteration 5): adding decreases clause to loop */
    let mut max_height: i8 = heights[0];
    let mut i: usize = 1;
    
    while i < n as usize
        invariant
            1 <= i <= n as usize,
            n as usize == heights.len(),
            max_height as int == max_in_seq(heights@.map(|j, x: i8| x as int).subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> heights[j] <= max_height
        decreases n as usize - i
    {
        if heights[i] > max_height {
            max_height = heights[i];
        }
        
        proof {
            let full_seq = heights@.map(|j, x: i8| x as int);
            let sub_old = full_seq.subrange(0, i as int);
            let sub_new = full_seq.subrange(0, (i + 1) as int);
            
            assert(sub_new.len() == i + 1);
            assert(sub_new[i as int] == heights[i as int] as int);
            assert forall|j: int| 0 <= j < i implies sub_new[j] == sub_old[j] by {
                assert(sub_new[j] == sub_old[j]);
            }
            
            if heights[i as int] as int > max_in_seq(sub_old) {
                assert(max_in_seq(sub_new) == heights[i as int] as int);
            } else {
                assert(max_in_seq(sub_new) == max_in_seq(sub_old));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        let full_seq = heights@.map(|j, x: i8| x as int);
        assert(full_seq.subrange(0, n as int) =~= full_seq);
        max_in_seq_properties(full_seq);
    }
    
    max_height
}
// </vc-code>


}

fn main() {}