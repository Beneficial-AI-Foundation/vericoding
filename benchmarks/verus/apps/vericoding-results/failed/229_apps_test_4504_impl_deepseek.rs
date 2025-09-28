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

proof fn lemma_even_substrings(s: Seq<char>, i: int)
    requires
        i >= 0,
        i <= s.len(),
        i % 2 == 0,
        valid_solution(s, i)
    ensures
        is_even_string(s.subrange(0, i)),
{
}

proof fn lemma_maximal_implies_no_larger(s: Seq<char>, result: int)
    requires
        is_maximal_solution(s, result),
    ensures
        forall|k: int| result < k < s.len() && k % 2 == 0 ==> !is_even_string(s.subrange(0, k)),
{
}

spec fn compute_possible_solution(s: Seq<char>) -> int {
    s.len()
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
    let mut max_even = 2;
    
    proof {
        lemma_even_substrings(s@, max_even as int);
    }
    
    let mut k: usize = 4;
    while k <= s.len() && k % 2 == 0
        invariant
            k % 2 == 0,
            max_even % 2 == 0,
            max_even >= 2,
            max_even <= k,
            k <= s.len(),
            valid_solution(s@, max_even as int),
            forall|i: int| 2 <= i < k as int && i % 2 == 0 ==> !is_even_string(s@.subrange(0, i)) || i <= max_even as int,
        decreases s.len() - k,
    {
        if k <= s.len() {
            let half = k / 2;
            let first_half = &s[0..half];
            let second_half = &s[half..k];
            
            if first_half == second_half {
                proof {
                    lemma_even_substrings(s@, k as int);
                }
                max_even = k;
            }
            
            k += 2;
        }
    }
    
    proof {
        lemma_maximal_implies_no_larger(s@, max_even as int);
    }
    
    max_even
}
// </vc-code>


}

fn main() {}