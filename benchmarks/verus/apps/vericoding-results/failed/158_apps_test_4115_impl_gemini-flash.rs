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
/* helper modified by LLM (iteration 5): [remove `count_mismatches_up_to_i` since `mismatches` is not a ghost variable] */
spec fn count_mismatches_loop_condition(s: Seq<char>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        let n = s.len() as int - 1;
        let mismatch: int = if i > 0 && i <= s.len() && s[i-1] != s[n - (i-1)] { 1 } else { 0 };
        count_mismatches_loop_condition(s, i-1) + mismatch
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [renamed `count_mismatches_upto_real` to `count_mismatches_loop_condition` to match helper function name] */
{
    let s_len: usize = s.len();
    let mut mismatches: i8 = 0;
    let mut i: usize = 0;

    while i < s_len / 2
        invariant
            0 <= i as int,
            i as int <= s_len as int / 2,
            mismatches as int == count_mismatches_loop_condition(s@, i as int) as int,
            s_len == s@.len(),
            valid_input(s@),
    {
        if s[i] != s[s_len - 1 - i] {
            mismatches = (mismatches + 1) as i8;
        }
        i = i + 1;
    }
    
    proof {
        assert(count_mismatches(s@) == count_mismatches_loop_condition(s@, s_len as int / 2) * 2);
    }

    mismatches
}
// </vc-code>


}

fn main() {}