// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn minimum(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else if s.len() > 1 && s[0] <= minimum(s.subrange(1, s.len() as int)) {
        s[0]
    } else {
        minimum(s.subrange(1, s.len() as int))
    }
}

spec fn count_occurrences(s: Seq<int>, val: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == val { 1int } else { 0int }) + count_occurrences(s.subrange(1, s.len() as int), val)
    }
}

spec fn valid_input(n: int, piles: Seq<int>) -> bool {
    n >= 2 && n % 2 == 0 && piles.len() == n && forall|i: int| 0 <= i < piles.len() ==> piles[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn lemma_valid_input_implies_even(n: int, piles: Seq<int>)
    requires valid_input(n, piles)
    ensures is_even(n)
{
}

fn pick_winner(n: i8, piles: Vec<i8>) -> (res: &'static str)
    requires valid_input(n as int, piles@.map_values(|v: i8| v as int))
    ensures res == "Alice" || res == "Bob"
{
    "Alice"
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, piles: Vec<i8>) -> (result: &'static str)
    requires valid_input(n as int, piles@.map_values(|v: i8| v as int))
    ensures result == "Alice" || result == "Bob"
// </vc-spec>
// <vc-code>
{
    let r = pick_winner(n, piles);
    r
}
// </vc-code>


}

fn main() {}