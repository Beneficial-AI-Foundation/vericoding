use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    
    // Calculate using usize arithmetic directly
    let count: usize = (n * (n + 1)) / 2;
    
    // Prove that the result matches the specification
    assert(count == (s.len() * (s.len() + 1)) / 2);
    
    count
}
// </vc-code>

fn main() {
}

}