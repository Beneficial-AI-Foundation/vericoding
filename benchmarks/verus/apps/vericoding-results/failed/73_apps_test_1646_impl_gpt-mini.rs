// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1') &&
    (s == seq!['0'] || s[0] == '1')
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0int
    } else { 
        (if s[0] == '0' { 1int } else { 0int }) + count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn create_zero_seq(n: nat) -> Seq<char> {
    Seq::new(n, |i: int| '0')
}

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'] + create_zero_seq(count_zeros(s) as nat))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove count_zeros is non-negative */
proof fn count_zeros_nonneg(s: Seq<char>)
    ensures
        count_zeros(s) >= 0,
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(count_zeros(s) == 0);
    } else {
        count_zeros_nonneg(s.subrange(1, s.len() as int));
        let rest = count_zeros(s.subrange(1, s.len() as int));
        if s[0] == '0' {
            assert(1 + rest >= 0);
        } else {
            assert(rest >= 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n as usize,
        valid_binary_string(s@),
    ensures 
        valid_binary_string(result@),
        is_minimal_form(s@, result@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute minimal form ("0" stays, else "1" followed by zeros) */
    if s@ == seq!['0'] {
        let result: Vec<char> = Vec::from_seq(seq!['0']);
        result
    } else {
        let zeros = count_zeros(s@);
        proof {
            count_zeros_nonneg(s@);
        }
        let res_seq: Seq<char> = seq!['1'] + create_zero_seq(zeros as nat);
        let result: Vec<char> = Vec::from_seq(res_seq);
        result
    }
}
// </vc-code>


}

fn main() {}