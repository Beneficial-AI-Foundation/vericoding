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
proof fn compute_indices(s: Seq<char>) -> (res: Seq<int>)
    requires valid_input(s)
    ensures res.len() == expected_length(s), 
        forall|i: int| 0 <= i < res.len() ==> res[i] == 2 * i
{
    let mut indices = Seq::<int>::empty();
    let mut i: nat = 0;
    let n = expected_length(s);
    while i < n
        invariant
            indices.len() == i as int,
            forall|j: int| 0 <= j < indices.len() ==> indices[j] == 2 * j
        decreases n - i
    {
        indices = indices.push((2 * i) as int);
        i = i + 1;
    }
    indices
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat/int conversion and indexing */
    let mut result = Vec::new();
    let n = (s.len() + 1) / 2;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[2 * j],
            correct_extraction(s@, result@)
        decreases n - i
    {
        result.push(s[2 * i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}