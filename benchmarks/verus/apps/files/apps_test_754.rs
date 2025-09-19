// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool
{
    n >= 1 && s.len() == n
}

spec fn count_adjacent_same_pairs(s: Seq<char>, n: int) -> int
{
    count_adjacent_same_pairs_up_to(s, n)
}

spec fn count_adjacent_same_pairs_up_to(s: Seq<char>, i: int) -> int
    decreases i
{
    if i <= 1 { 0int }
    else { (if s[i-1] == s[i-2] { 1int } else { 0int }) + count_adjacent_same_pairs_up_to(s, i-1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: i8)
    requires 
        valid_input(n as int, s@),
    ensures 
        result >= 0,
        result <= n - 1,
        result as int == count_adjacent_same_pairs(s@, n as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}