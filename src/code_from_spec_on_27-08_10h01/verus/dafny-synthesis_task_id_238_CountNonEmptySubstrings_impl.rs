use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn num_substrings(n: nat) -> nat {
    n * (n + 1) / 2
}

proof fn substring_count_lemma(n: nat)
    ensures num_substrings(n) == n * (n + 1) / 2
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let len = s.len();
    let count = len * (len + 1) / 2;
    
    proof {
        substring_count_lemma(len);
    }
    
    count
}
// </vc-code>

fn main() {
}

}