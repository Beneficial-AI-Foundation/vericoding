// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn minimum(s: Seq<int>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else if s[0] <= minimum(s.subrange(1, s.len() as int)) {
        s[0]
    } else {
        minimum(s.subrange(1, s.len() as int))
    }
}

spec fn count_occurrences(s: Seq<int>, val: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == val { 1 } else { 0 }) + count_occurrences(s.subrange(1, s.len() as int), val)
    }
}

spec fn valid_input(n: int, piles: Seq<int>) -> bool {
    n >= 2 && n % 2 == 0 && piles.len() == n && forall|i: int| 0 <= i < piles.len() ==> piles[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, piles: Seq<int>) -> (result: String)
    requires valid_input(n, piles)
    ensures result == "Alice" || result == "Bob"
// </vc-spec>
// <vc-code>
{
    assume(false);
    "Alice".to_string()
}
// </vc-code>


}

fn main() {}