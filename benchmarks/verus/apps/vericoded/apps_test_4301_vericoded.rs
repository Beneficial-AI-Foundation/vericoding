// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_of_seq(s: Seq<int>) -> int
    recommends s.len() >= 1
{
    if s.len() == 1 {
        s[0]
    } else {
        if s[0] >= s[1] {
            s[0]
        } else {
            s[1]
        }
    }
}

spec fn max_excluding(s: Seq<int>, exclude_idx: int) -> int
    recommends 0 <= exclude_idx < s.len() && s.len() >= 2
{
    if exclude_idx == 0 {
        max_of_seq(s.subrange(1, s.len() as int))
    } else if exclude_idx == s.len() - 1 {
        max_of_seq(s.subrange(0, s.len() - 1))
    } else {
        max_of_seq(s.subrange(0, exclude_idx).add(s.subrange(exclude_idx + 1, s.len() as int)))
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn to_int_i8(x: i8) -> int {
    x as int
}

spec fn from_int_i8(x: int) -> i8
    recommends
        -128 <= x <= 127,
{
    x as i8
}

proof fn lemma_len_ge2_implies_ge1(s: Seq<int>)
    requires
        s.len() >= 2,
    ensures
        s.len() >= 1,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input@.len() >= 2
// </vc-spec>
// <vc-code>
{
    input
}
// </vc-code>


}

fn main() {}