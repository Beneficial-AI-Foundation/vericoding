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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, piles: Vec<i8>) -> (result: &'static str)
    requires valid_input(n as int, piles@.map_values(|v: i8| v as int))
    ensures result == "Alice" || result == "Bob"
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Remove unused view to fix compilation, add usize casts for indexing, 구현 XOR loop to determine winner */
    let mut xor_val: i8 = 0;
    let mut i: usize = 0;
    while i < piles.len()
        invariant
            i <= piles.len(),
        decreases piles.len() - i
    {
        xor_val ^= piles[i];
        i += 1;
    }
    if xor_val == 0 {
        "Bob"
    } else {
        "Alice"
    }
}
// </vc-code>


}

fn main() {}