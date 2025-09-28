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
/* helper modified by LLM (iteration 3): fixed type conversion in subrange call */
spec fn extract_chars(s: Seq<char>) -> (result: Seq<char>)
    requires valid_input(s)
    ensures correct_extraction(s, result)
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        let tail = extract_chars(s.subrange(2, s.len() as int));
        Seq::new(1, |i: int| s[0]) + tail
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implemented correct extraction logic */
{
    let n = (s.len() + 1) / 2;
    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        result.push(s[2 * i]);
    }
    result
}
// </vc-code>


}

fn main() {}