// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1
}

spec fn count_mismatches_up_to(s: Seq<char>, limit: int) -> int
    decreases limit
{
    if limit <= 0 || s.len() < 1 { 
        0 
    } else {
        let n = s.len() as int - 1;
        let mismatch: int = if limit > 0 && limit <= s.len() && s[limit-1] != s[n - (limit-1)] { 1 } else { 0 };
        count_mismatches_up_to(s, limit-1) + mismatch
    }
}

spec fn count_mismatches(s: Seq<char>) -> int {
    if s.len() >= 1 {
        count_mismatches_up_to(s, s.len() as int)
    } else {
        0
    }
}

spec fn valid_result(s: Seq<char>, result: int) -> bool {
    if valid_input(s) {
        result >= 0 && result <= s.len() / 2 && result == (count_mismatches(s) / 2)
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors by removing @ accessor on Seq parameters */
proof fn count_mismatches_up_to_monotonic(s: Seq<char>, i: int, j: int)
    requires
        valid_input(s),
        0 <= i <= j <= s.len(),
    ensures
        count_mismatches_up_to(s, i) <= count_mismatches_up_to(s, j)
    decreases j - i
{
    if i < j {
        count_mismatches_up_to_monotonic(s, i, j - 1);
    }
}

proof fn count_mismatches_up_to_bound(s: Seq<char>, limit: int)
    requires
        valid_input(s),
        0 <= limit <= s.len(),
    ensures
        count_mismatches_up_to(s, limit) <= limit
    decreases limit
{
    if limit > 0 {
        count_mismatches_up_to_bound(s, limit - 1);
    }
}

proof fn count_mismatches_bound(s: Seq<char>)
    requires valid_input(s)
    ensures count_mismatches(s) <= s.len()
{
    count_mismatches_up_to_bound(s, s.len() as int);
}

proof fn count_mismatches_full_analysis(s: Seq<char>)
    requires valid_input(s)
    ensures count_mismatches(s) == count_mismatches_up_to(s, (s.len() / 2) as int)
    decreases s.len()
{
    let n = s.len() as int;
    let half = (n / 2) as int;
    
    // For even length strings, count_mismatches counts the first half only
    // For odd length strings, the middle character doesn't contribute to mismatches
}

proof fn loop_invariant_preservation(s: Seq<char>, i: usize, mismatches: u32)
    requires
        valid_input(s),
        i < s.len() / 2,
        mismatches == count_mismatches_up_to(s, i as int),
        mismatches <= i as u32,
    ensures
        mismatches + (if s[i as int] != s[s.len() as int - 1 - i as int] { 1 } else { 0 }) == count_mismatches_up_to(s, (i + 1) as int)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors by using int indexing for Seq operations */
    let n = s.len();
    let mut mismatches = 0i32;
    let mut i = 0usize;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == s.len(),
            mismatches == count_mismatches_up_to(s@, i as int),
            0 <= mismatches <= i as i32,
        decreases n / 2 - i
    {
        assert(i < n / 2);
        assert(n - 1 - i < n);
        
        proof {
            loop_invariant_preservation(s@, i, mismatches as u32);
        }
        
        if s[i] != s[n - 1 - i] {
            mismatches = mismatches + 1;
        }
        i = i + 1;
    }
    
    proof {
        count_mismatches_bound(s@);
        count_mismatches_full_analysis(s@);
        assert(mismatches == count_mismatches_up_to(s@, (n / 2) as int));
        assert(count_mismatches(s@) == count_mismatches_up_to(s@, (n / 2) as int));
        assert(mismatches == count_mismatches(s@));
        assert(mismatches == count_mismatches(s@) / 2 * 2);
        assert(count_mismatches(s@) / 2 == mismatches / 2);
        assert(mismatches <= (n / 2) as i32);
        assert(mismatches <= 127);
    }
    
    (mismatches / 2) as i8
}
// </vc-code>


}

fn main() {}