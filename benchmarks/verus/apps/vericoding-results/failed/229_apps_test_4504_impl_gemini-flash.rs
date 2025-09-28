// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_even_string(s: Seq<char>) -> bool {
    s.len() >= 2 && s.len() % 2 == 0 && s.subrange(0, s.len() as int / 2) == s.subrange(s.len() as int / 2, s.len() as int)
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 2 && is_even_string(s)
}

spec fn valid_solution(s: Seq<char>, result: int) -> bool {
    2 <= result < s.len() && result % 2 == 0 && is_even_string(s.subrange(0, result))
}

spec fn is_maximal_solution(s: Seq<char>, result: int) -> bool {
    valid_solution(s, result) && 
    forall|k: int| result < k < s.len() && k % 2 == 0 ==> !is_even_string(s.subrange(0, k))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@) &&
        (exists|k: int| valid_solution(s@, k))
    ensures 
        valid_solution(s@, result as int) &&
        is_maximal_solution(s@, result as int)
// </vc-spec>
// <vc-code>
{
    let s_seq = s@;
    let mut result: usize = 0;
    let mut current_len: usize = 0;

    while current_len <= s_seq.len()
        invariant 
            0 <= current_len,
            current_len <= s_seq.len(),
            current_len % 2 == 0,
            0 <= result,
            result <= current_len,
            result % 2 == 0,
            (result == 0 && current_len < 2) || (result > 0 && is_even_string(s_seq.subrange(0, result as int))),
            forall|k: int| result < k && k < current_len && k % 2 == 0 ==> !is_even_string(s_seq.subrange(0, k)),
        decreases (s_seq.len() - current_len)
    {
        if current_len >= 2 && current_len % 2 == 0 {
            if is_even_string(s_seq.subrange(0, current_len as int)) {
                result = current_len;
            }
            proof {
                if current_len > 0 && current_len % 2 == 0 && current_len as int == result as int && is_even_string(s_seq.subrange(0, current_len as int)) {
                    assert(is_even_string(s_seq.subrange(0, result as int)));
                }
            }
        }
        current_len = current_len + 2;
    }
    
    proof {
        if s_seq.len() >= 2 {
            assert(forall|k: int| result < k && k < s_seq.len() && k % 2 == 0 ==> !is_even_string(s_seq.subrange(0, k))) by {
                let mut current_proof_k: int = (result as int) + 2;
                while current_proof_k < s_seq.len()
                    invariant
                        result < current_proof_k,
                        current_proof_k <= s_seq.len() + 1,
                        current_proof_k % 2 == 0,
                        forall|j: int| result < j && j < current_proof_k && j % 2 == 0 ==> !is_even_string(s_seq.subrange(0, j)),
                    decreases (s_seq.len() - current_proof_k)
                {
                    if current_proof_k < s_seq.len() {
                        assert(!is_even_string(s_seq.subrange(0, current_proof_k)));
                    }
                    current_proof_k = current_proof_k + 2;
                }
            }
        }
    }

    result
}
// </vc-code>


}

fn main() {}