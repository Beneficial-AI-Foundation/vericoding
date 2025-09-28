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
    /* code modified by LLM (iteration 3): fixed literal typing to use 0int and added as int cast in decreases for proper integer arithmetic */
    let mut result = Vec::new();
    let mut i = 0int;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            i % 2 == 0,
            result@.len() == i / 2,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[2 * j],
        decreases ((s@.len() as int - i) / 2)
    {
        result.push(s@[i]);
        i = i + 2;
    }
    result
}
// </vc-code>


}

fn main() {}