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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, heights@.map(|i, x: i8| x as int))
    ensures valid_result(n as int, heights@.map(|i, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed int/nat type casts to ghost variables. */
    let ghost sn = n as int;
    let ghost sheights = heights@.map(|i, x: i8| x as int);

    let mut i: i8 = 0;
    let mut max_val: i8 = 0;

    if n > 0 {
        max_val = heights[0];
    }

    while (i as int) < sn
        invariant
            0 <= i as int,
            i as int <= sn,
            sn > 0 ==> (i as int == 0 ==> max_val as int == sheights[0]),
            sn > 0 ==> (i as int > 0 ==> max_val as int == max_in_seq(sheights.subrange(0, i as int))),
            forall|j: int| 0 <= j < i as int ==> sheights[j] <= (max_val as int),
        decreases sn - (i as int)
    {
        if heights[i as usize] > max_val {
            max_val = heights[i as usize];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>


}

fn main() {}