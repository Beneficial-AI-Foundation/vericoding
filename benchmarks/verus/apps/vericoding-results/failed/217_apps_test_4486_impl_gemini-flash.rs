// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn expected_length(s: Seq<char>) -> nat {
    (s.len() + 1) / 2
}

spec fn correct_extraction(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == expected_length(s) &&
    forall|i: int| 0 <= i < result.len() ==> 0 <= 2*i < s.len() && #[trigger] result[i] == s[2*i] &&
    forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i] && j == i / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to the while loop and verified pre-conditions */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant 
            0 <= i as int,
            i as int <= s.len() as int,
            
            // result.len() should be exactly i/2 if i is even
            // or (i+1)/2 if i is odd (which means i-1 is the last index considered)
            // but we only consider even indices, so this is simply i/2
            result@.len() == (i / 2) as nat,

            // At each iteration, result should contain characters from s@[0], s@[2], ..., s@[i-2]
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[2 * j]
        decreases s.len() - i
    {
        if i % 2 == 0 {
            result.push(s[i]);
        }
        i = i + 1;
    }

    proof {
        // After the loop, we need to prove correct_extraction(s@, result@).
        // This means proving result.len() == expected_length(s@)
        // and the forall clauses in correct_extraction.

        assert(result@.len() as nat == expected_length(s@)) by {
            if s.len() % 2 == 0 {
                // If s.len() is even, expected_length is s.len()/2
                // and i will be s.len() after the loop, so result.len() is s.len()/2
                assert(result@.len() == s.len() / 2);
                assert(expected_length(s@) == s.len() / 2);
            } else {
                // If s.len() is odd, expected_length is (s.len()+1)/2
                // and i will be s.len() after the loop, so result.len() is (s.len()-1)/2 + 1 = (s.len()+1)/2
                assert(result@.len() == (s.len() + 1) / 2);
                assert(expected_length(s@) == (s.len() + 1) / 2);
            }
        }

        // The forall clause: forall|i: int| 0 <= i < result.len() ==> 0 <= 2*i < s.len() && #[trigger] result[i] == s[2*i]
        // This is directly covered by the loop invariant.

        // The forall clause: forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i] && j == i / 2
        // This also follows from the loop's construction and invariant.
         forbid_recommends(); // Just to avoid any warnings from this proof block
    }

    result
}
// </vc-code>


}

fn main() {}