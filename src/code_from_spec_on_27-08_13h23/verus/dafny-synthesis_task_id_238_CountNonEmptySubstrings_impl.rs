use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to compute the number of non-empty substrings
proof fn lemma_substring_count(n: usize)
    ensures
        (n * (n + 1)) / 2 >= 0,
        (n * (n + 1)) / 2 == if n == 0 { 0 } else { n + ((n - 1) * n) / 2 },
{
    if n > 0 {
        assert((n * (n + 1)) / 2 == n + ((n - 1) * n) / 2) by {
            // Verus can prove this arithmetic equality
        }
    }
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
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2,
{
    let n = s.len();
    proof {
        lemma_substring_count(n);
    }
    let count = (n * (n + 1)) / 2;
    count
}
// </vc-code>

fn main() {
}

}