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
    /* code modified by LLM (iteration 5): Added trigger annotation for exists quantifier */
    let n = s.len();
    
    // Initialize result to 2 and verify it's valid
    let mut result: usize = 2;
    assert(s@.subrange(0, 1) == s@.subrange(1, 2)); // First 2 chars form even string
    assert(is_even_string(s@.subrange(0, 2)));
    assert(valid_solution(s@, 2));
    
    let mut i: usize = 4;
    while i <= n
        invariant
            n == s.len(),
            n >= 2,
            n % 2 == 0,
            4 <= i <= n + 2,
            i % 2 == 0,
            2 <= result < n,
            result % 2 == 0,
            valid_solution(s@, result as int),
            forall|k: int| #![auto] result < k < i - 2 && k % 2 == 0 ==> !is_even_string(s@.subrange(0, k)),
        decreases n - i
    {
        if i > n {
            break;
        }
        
        let half = i / 2;
        let mut is_match = true;
        let mut j: usize = 0;
        
        while j < half
            invariant
                0 <= j <= half,
                half == i / 2,
                i <= n,
                half + j <= n,
                is_match ==> s@.subrange(0, j as int) == s@.subrange(half as int, half as int + j as int),
                !is_match ==> exists|m: nat| #[trigger] (m < j) && s@[m as int] != s@[half as int + m as int],
            decreases half - j
        {
            if s[j] != s[half + j] {
                is_match = false;
                break;
            }
            j = j + 1;
        }
        
        if is_match {
            assert(j == half);
            assert(s@.subrange(0, half as int) == s@.subrange(half as int, half as int + half as int));
            assert(s@.subrange(0, half as int) == s@.subrange(half as int, i as int));
            assert(i == 2 * half);
            assert(is_even_string(s@.subrange(0, i as int)));
            assert(valid_solution(s@, i as int));
            result = i;
        }
        
        i = i + 2;
    }
    
    assert(forall|k: int| #![auto] result < k < n && k % 2 == 0 ==> !is_even_string(s@.subrange(0, k)));
    result
}
// </vc-code>


}

fn main() {}