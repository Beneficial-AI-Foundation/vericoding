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
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* impl-start */
    assume(false);
    unreached()
    /* impl-end */
}
// </vc-code>


}

fn main() {}