// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_characters(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == s.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented a while loop to correctly convert the nat sequence length to a usize count */
    let mut count: usize = 0;
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            count as nat == i,
        decreases s.len() - i
    {
        count = count + 1;
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}