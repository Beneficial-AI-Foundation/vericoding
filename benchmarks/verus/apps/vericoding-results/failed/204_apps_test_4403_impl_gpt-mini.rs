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
/* helper modified by LLM (iteration 5): computes sum of suffix starting at index i */
spec fn compute_sum_from_seq(s: Seq<char>, i: int) -> int
    requires
        0 <= i,
        i <= s.len(),
    ensures
        result == calculate_sum(s.subrange(i, s.len())),
    decreases
        s.len() - i
{
    if i == s.len() {
        0
    } else {
        (if s[i] == '+' { 1 } else { -1 }) + compute_sum_from_seq(s, i+1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using usize indices and maintain invariant relating acc to spec */
    let mut i: usize = s.len();
    let mut acc: i8 = 0;
    while i > 0
        invariant
            0 <= i as int,
            i as int <= s.len(),
            acc as int == compute_sum_from_seq(s@, i as int),
        decreases
            i as int
    {
        let idx: usize = i - 1;
        let ch: char = s[idx];
        proof {
            assert(s@[idx as int] == ch);
            assert(acc as int == compute_sum_from_seq(s@, i as int));
            assert((if ch == '+' { 1 } else { -1 }) + compute_sum_from_seq(s@, i as int) == compute_sum_from_seq(s@, (i - 1) as int));
        }
        if ch == '+' {
            acc = acc + 1;
        } else {
            acc = acc - 1;
        }
        i = idx;
        proof {
            assert(acc as int == compute_sum_from_seq(s@, i as int));
        }
    }
    proof {
        assert(i == 0usize);
        assert(acc as int == compute_sum_from_seq(s@, 0));
    }
    acc
}
// </vc-code>


}

fn main() {}