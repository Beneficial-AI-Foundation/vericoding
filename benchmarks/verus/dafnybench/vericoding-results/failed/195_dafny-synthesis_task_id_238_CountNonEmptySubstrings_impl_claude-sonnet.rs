use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if n == 0 {
        proof {
            assert(n * (n + 1) / 2 == 0);
        }
        0
    } else {
        let result = (n * (n + 1)) / 2;
        proof {
            // For a string of length n, the number of non-empty substrings is:
            // - n substrings of length 1
            // - (n-1) substrings of length 2  
            // - (n-2) substrings of length 3
            // - ...
            // - 1 substring of length n
            // Total = n + (n-1) + (n-2) + ... + 1 = n*(n+1)/2
            assert(result == n * (n + 1) / 2);
        }
        result
    }
}
// </vc-code>

fn main() {
}

}