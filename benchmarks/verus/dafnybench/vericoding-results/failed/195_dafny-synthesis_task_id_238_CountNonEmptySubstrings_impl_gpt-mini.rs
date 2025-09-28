use vstd::prelude::*;

verus! {

// <vc-helpers>
fn nat_to_usize(n: nat) -> usize {
    n as usize
}
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n: usize = nat_to_usize(s.len());
    let count: usize = n * (n + 1) / 2;
    count
}
// </vc-code>

fn main() {
}

}