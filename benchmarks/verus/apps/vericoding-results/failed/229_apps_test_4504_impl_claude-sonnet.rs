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
spec fn check_even_string_at_length(s: Seq<char>, len: int) -> bool {
    len >= 2 && len % 2 == 0 && len <= s.len() &&
    s.subrange(0, len / 2) == s.subrange(len / 2, len)
}

proof fn lemma_even_string_equivalence(s: Seq<char>, len: int)
    requires
        len >= 2,
        len % 2 == 0,
        len <= s.len()
    ensures
        check_even_string_at_length(s, len) <==> is_even_string(s.subrange(0, len))
{
}

proof fn lemma_maximal_property(s: Seq<char>, result: int)
    requires
        valid_solution(s, result),
        result + 2 <= s.len(),
        !check_even_string_at_length(s, result + 2)
    ensures
        is_maximal_solution(s, result)
{
}
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
    /* code modified by LLM (iteration 5): Fixed quantifier trigger annotation */
    let mut result: usize = 2;
    
    while result + 2 <= s.len()
        invariant
            2 <= result,
            result % 2 == 0,
            result <= s.len(),
            check_even_string_at_length(s@, result as int),
            forall|k: int| 2 <= k < result && k % 2 == 0 ==> check_even_string_at_length(s@, k)
        decreases s.len() - result
    {
        let next_len = result + 2;
        let half = next_len / 2;
        
        let mut is_match = true;
        let mut i = 0;
        
        while i < half
            invariant
                0 <= i <= half,
                half == next_len / 2,
                next_len == result + 2,
                is_match == (forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == #[trigger] s@[j + half])
            decreases half - i
        {
            if s[i] != s[i + half] {
                is_match = false;
                break;
            }
            i += 1;
        }
        
        if !is_match {
            break;
        }
        
        result = next_len;
    }
    
    proof {
        lemma_maximal_property(s@, result as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}