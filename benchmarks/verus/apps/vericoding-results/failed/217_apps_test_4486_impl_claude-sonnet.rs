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
/* helper modified by LLM (iteration 5): Changed proves_final_correctness to spec function */
spec fn lemma_i_in_bounds(i: usize, s_len: usize) -> bool
{
    (i % 2 == 0 && i < s_len) ==> (i + 2 <= s_len || i + 2 > s_len)
}

spec fn proves_final_correctness(s: Seq<char>, result: Seq<char>, final_i: int) -> bool
{
    valid_input(s) &&
    final_i >= s.len() &&
    final_i % 2 == 0 &&
    result.len() == final_i / 2 &&
    (forall|j: int| 0 <= j < result.len() ==> 0 <= 2*j < s.len() && result[j] == s[2*j]) &&
    correct_extraction(s, result)
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_extraction(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed exec call to proves_final_correctness */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            i % 2 == 0,
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> 0 <= 2*j < s.len() && result@[j] == s@[2*j]
        decreases s.len() - i
    {
        result.push(s[i]);
        
        proof {
            if i + 2 <= s.len() {
                assert((i + 2) % 2 == 0);
                assert(result.len() == (i + 2) / 2);
            }
        }
        
        if i + 2 <= s.len() {
            i += 2;
        } else {
            break;
        }
    }
    
    proof {
        assert(i >= s.len());
        assert(result.len() == expected_length(s@));
        assert(forall|j: int| 0 <= j < result.len() ==> 0 <= 2*j < s.len() && result@[j] == s@[2*j]);
        assert(forall|k: int| 0 <= k < s.len() && k % 2 == 0 ==> exists|j: int| 0 <= j < result.len() && result@[j] == s@[k] && j == k / 2);
    }
    
    result
}
// </vc-code>


}

fn main() {}