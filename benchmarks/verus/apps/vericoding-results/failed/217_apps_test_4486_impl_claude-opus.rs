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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            i % 2 == 0,
            result@.len() == i / 2,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[2*j],
            forall|j: int| 0 <= j < i && j % 2 == 0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == s@[j] && k == j / 2,
        decreases s.len() - i
    {
        result.push(s[i]);
        
        proof {
            assert(result@.len() == i / 2 + 1);
            assert(result@[result@.len() - 1] == s@[i]);
            assert(2 * (result@.len() - 1) == i);
            assert(forall|j: int| 0 <= j < result@.len() - 1 ==> result@[j] == s@[2*j]);
            assert(forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[2*j]);
        }
        
        if i + 2 < s.len() {
            i = i + 2;
        } else {
            i = s.len();
        }
    }
    
    proof {
        assert(i == s.len());
        assert(result@.len() == (s@.len() + 1) / 2);
        assert(result@.len() == expected_length(s@));
    }
    
    result
}
// </vc-code>


}

fn main() {}