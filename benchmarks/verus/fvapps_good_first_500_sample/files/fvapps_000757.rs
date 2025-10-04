// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd_two(a: u32, b: u32) -> u32 
    decreases vstd::math::max(a as int, b as int)
{
    if b == 0 {
        a
    } else {
        gcd_two(b, a % b)
    }
}

spec fn gcd_seq(s: Seq<u32>) -> u32
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        gcd_two(s[0], gcd_seq(s.skip(1)))
    }
}

spec fn min_two(a: u32, b: u32) -> u32 {
    if a <= b { a } else { b }
}

spec fn min_seq(s: Seq<u32>) -> u32 
    decreases s.len()
{
    if s.len() == 0 {
        u32::MAX
    } else if s.len() == 1 {
        s[0]
    } else {
        min_two(s[0], min_seq(s.skip(1)))
    }
}

spec fn solve_sequence_spec(d: u32) -> Seq<u32>;

fn solve_sequence(d: u32) -> (result: Vec<u32>)
    ensures
        result.len() >= 1 && result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 1 && result[i] <= 100000,
        result@ == solve_sequence_spec(d)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}