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
#[verifier::spinoff_prover]
proof fn lemma_even_index_in_bounds(i: int, s_len: int)
    requires
        s_len >= 1,
        0 <= i,
        i < (s_len + 1) / 2,
    ensures
        2 * i < s_len,
{
}

#[verifier::spinoff_prover]
proof fn lemma_half_lt_half_plus_one(k: int, s_len: int)
    requires
        s_len >= 1,
        0 <= k < s_len,
    ensures
        k / 2 < (s_len + 1) / 2,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    let expected_len = expected_length(s@);

    while i < expected_len
        invariant
            0 <= i <= expected_len,
            result@.len() == i as nat,
            expected_len == expected_length(s@),
            forall|j: int| 0 <= j < i ==> 
                0 <= 2*j < s@.len() && result@[j] == s@[2*j],
        decreases expected_len - i
    {
        proof {
            lemma_even_index_in_bounds(i as int, s@.len() as int);
        }

        result.push(s[2 * i]);
        i = i + 1;
    }

    proof {
        assert forall|k: int| 0 <= k < s@.len() && k % 2 == 0
        implies (exists|j: int|
            0 <= j < result@.len() &&
            result@[j] == s@[k] &&
            j == k / 2
        ) by {
            let j = k / 2;

            lemma_half_lt_half_plus_one(k, s@.len() as int);
            assert(j < result@.len());

            vstd::arithmetic::div_mod::lemma_div_relation(k, 2);
            assert(k == 2*j);
            assert(result@[j] == s@[k]);
        }
    }

    result
}
// </vc-code>


}

fn main() {}