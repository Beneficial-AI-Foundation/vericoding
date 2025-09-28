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
/* helper modified by LLM (iteration 5): predicate for lowercase characters */
spec fn is_lowercase(c: char) -> bool {
    'a' <= c && c <= 'z'
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result by iterating expected_length and maintain index bounds invariant */
    let mut res: Vec<char> = Vec::new();
    let n: usize = s.len();
    let exp: usize = expected_length(s@) as usize;
    let mut j: usize = 0;

    while j < exp
        invariant
            res.len() == j,
            2*j < n,
            forall|k: int| 0 <= k < j as int ==> 0 <= 2*k < s@.len() && res@[k] == s@[2*k],
        decreases exp - j
    {
        let idx: usize = 2 * j;
        let c: char = s[idx];
        res.push(c);
        j = j + 1;
    }

    res
}
// </vc-code>


}

fn main() {}