use vstd::prelude::*;

verus! {

// <vc-helpers>
// no changes
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n = (s.len() * (s.len() + 1)) / 2;
    let count: usize = n as usize;
    assert((count as nat) == n);
    count
}
// </vc-code>

fn main() {
}

}