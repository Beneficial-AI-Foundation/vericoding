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
fn count_mismatches_exec(s: Seq<char>) -> (count: int)
    requires
        s.len() >= 1,
    ensures
        count == count_mismatches(s@),
{
    let mut i: usize = 0;
    let mut count = 0;
    let n = s.len();
    while i < n / 2
        invariant
            i <= n / 2,
            count == count_mismatches_up_to(s, i as int),
            count >= 0,
            i >= 0,
        decreases (n / 2) - i,
    {
        if s[i] != s[n - 1 - i] {
            count += 1;
        }
        proof {
            assert(i < n / 2);
        }
        i += 1;
    }
    proof {
        assert(count == count_mismatches(s));
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    let total_mismatches = count_mismatches_exec(s@);
    let result_int = total_mismatches / 2;
    proof {
        assert(result_int <= s.len() / 2);
        assert(valid_result(s@, result_int));
    }
    (result_int as i8)
}
// </vc-code>


}

fn main() {}