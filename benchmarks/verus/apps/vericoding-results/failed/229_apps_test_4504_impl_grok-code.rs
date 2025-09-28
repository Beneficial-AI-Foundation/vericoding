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
/* helper modified by LLM (iteration 5): Fixed compilation error by casting len to int in ensures specification */
fn is_even_prefix(s: &Vec<char>, len: usize) -> bool
    requires
        len <= s.len(),
        len % 2 == 0,
    ensures
        result <==> is_even_string(s@.subrange(0, len as int))
{
    let half = len / 2;
    let mut i = 0;
    let mut equal = true;
    
    while i < half
        invariant
            0 <= i <= half,
            equal ==> (forall |j: int| 0 <= j < i ==> s[j] == s[j + half]),
        decreases
            half - i
    {
        if s[i] != s[i + half] {
            equal = false;
        }
        i += 1;
    }
    
    equal
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
    /* code modified by LLM (iteration 5): Implemented the maximal even prefix search without verification bypasses */
    
    let mut k: usize = if s.len() % 2 == 0 { s.len() - 2 } else { s.len() - 1 };
    
    while k >= 2
        invariant
            k % 2 == 0,
            0 <= k <= s@.len() - 2,
            // No larger prefix is valid
            forall |j: int| k < j < s@.len() && j % 2 == 0 ==> !is_even_string(s@.subrange(0, j))
        decreases
            k
    {
        if is_even_prefix(&s, k) {
            proof {
                assert(is_even_string(s@.subrange(0, k)));
            }
            return k;
        }
        k -= 2;
    }
    
    // Since the pre ensures exists, the loop must have found it, but to satisfy the function, we return 2
    return 2
}
// </vc-code>


}

fn main() {}