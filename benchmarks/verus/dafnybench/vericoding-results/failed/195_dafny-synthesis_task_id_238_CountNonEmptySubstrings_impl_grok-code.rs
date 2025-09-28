use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n: usize = s.len() as usize;
    return (n * (n + 1)) / 2;
}
// </vc-code>

fn main() {
}

}