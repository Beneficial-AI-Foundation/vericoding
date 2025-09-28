// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 4 && forall|i: int| 0 <= i < s.len() ==> s[i] == '+' || s[i] == '-'
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0nat as int
    } else {
        (if s[0] == c { 1nat as int } else { 0nat as int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn calculate_sum(s: Seq<char>) -> int {
    count_char(s, '+') - count_char(s, '-')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removing helper as it was not needed by the latest implementation. */
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Changed loop condition `i as nat` to `i`, and removed unnecessary `s.get()` calls. */
{
    let mut plus_count: int = 0;
    let mut minus_count: int = 0;
    let mut i: int = 0;

    while i < s.len() as int
        invariant
            0 <= i <= s.len() as int,
            plus_count == count_char(s@.subrange(0, i as int), '+'),
            minus_count == count_char(s@.subrange(0, i as int), '-'),
            s.len() == 4,
            forall|j: int| 0 <= j < s.len() ==> (s@[j] == '+' || s@[j] == '-'),
        decreases s.len() as int - i
    {
        let current_char = s@[i as int];
        if current_char == '+' {
            plus_count = plus_count + 1;
        } else if current_char == '-' {
            minus_count = minus_count + 1;
        }
        i = i + 1;
    }

    proof {
        assert(plus_count == count_char(s@, '+'));
        assert(minus_count == count_char(s@, '-'));
    }

    let result_int: int = plus_count - minus_count;
    result_int as i8
}
// </vc-code>


}

fn main() {}