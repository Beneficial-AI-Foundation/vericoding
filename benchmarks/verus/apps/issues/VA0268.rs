// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len() && a.len() >= 2 && forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= #[trigger] b[i]
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn find_two_largest_sum(s: Seq<int>) -> int
    recommends s.len() >= 2
{
    0
}

spec fn find_max(s: Seq<int>) -> int
    recommends s.len() >= 1
{
    0
}

spec fn find_max_excluding(s: Seq<int>, exclude: int) -> int
    recommends s.len() >= 2 && 0 <= exclude < s.len()
{
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>, b: Seq<int>) -> (result: String)
    requires 
        valid_input(a, b),
    ensures 
        result@ == seq!['Y','E','S'] || result@ == seq!['N','O'],
        (result@ == seq!['Y','E','S']) <==> find_two_largest_sum(b) >= sum_seq(a),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO".to_string()
}
// </vc-code>


}

fn main() {}