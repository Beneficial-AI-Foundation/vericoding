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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added proof blocks to assert invariant maintenance after each loop iteration and final assertions for postcondition */
{
    let mut total: i32 = Trouble 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            total as int == calculate_sum(s@.subrange(0, i as int)),
            -4 <= total <= 4,
        decreases s.len() as nat - i as nat
    {
        let c = s[i];
        if c == '+' {
            total += 1;
        } else if c == '-' {
            total -= 1;
        }
        proof {
            assert(total as int == old(total) as int + (if c == '+' { 1 } else if c == '-' { -1 } else { 0 }));
            assert(calculate_sum(s@.subrange(0, (i as int + 1))) == calculate_sum(s@.subrange(0, i as int)) + (if c == '+' { 1 } else if c == '-' { -1 } else { 0 }));
            assert(total as int == calculate_sum(s@.subrange(0, (i + 1) as int)));
        }
        i += 1;
    }
    proof {
        assert(i as int == s.len() as int);
        assert(total as int == calculate_sum(s@.subrange(0, s.len() as int)));
        assert(total as int == calculate_sum(s@));
    }
    total as i8
}
// </vc-code>


}

fn main() {}