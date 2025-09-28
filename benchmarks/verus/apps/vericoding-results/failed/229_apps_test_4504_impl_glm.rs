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
/* helper modified by LLM (iteration 5): fixed compilation error by replacing slice comparison with explicit loop */
fn is_prefix_even_string_exec(s: &Vec<char>, candidate: usize) -> bool {
    if candidate < 2 || candidate % 2 != 0 || candidate > s.len() {
        return false;
    }
    let half = candidate / 2;
    let mut i = 0;
    while i < half
        invariant 0 <= i <= half
    {
        if s[i] != s[half + i] {
            return false;
        }
        i += 1;
    }
    true
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
/* code modified by LLM (iteration 5): maintained existing implementation logic */
{
    let mut candidate = s.len() - 2;
    while candidate >= 2
        invariant
            2 <= candidate <= s.len() && candidate % 2 == 0,
            forall|k: int| candidate < k < s.len() && k % 2 == 0 ==> !is_even_string(s@.subrange(0, k)),
            exists|k: int| 2 <= k <= candidate && k % 2 == 0 && is_even_string(s@.subrange(0, k)),
        decreases candidate
    {
        if is_prefix_even_string_exec(&s, candidate) {
            return candidate;
        }
        candidate -= 2;
    }
    2
}
// </vc-code>


}

fn main() {}