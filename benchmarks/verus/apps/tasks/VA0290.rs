// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 && exists|pos: int| 0 <= pos < stdin_input.len() && stdin_input[pos] == '\n'
}

spec fn valid_digit_string(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn valid_number_string(s: Seq<char>) -> bool {
    valid_digit_string(s) && s[0] != '0'
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() > 0 && forall|i: int| 0 <= i < result.len() ==> ('0' <= #[trigger] result[i] <= '9')
}

spec fn is_good_shift(s: Seq<char>, shift: int) -> bool 
    recommends 0 <= shift < s.len(), s.len() > 0
{
    s[shift] != '0'
}

spec fn cyclic_shift_remainder(s: Seq<char>, shift: int, m: int) -> int
    recommends 
        0 <= shift < s.len(),
        s.len() > 0,
        m >= 2,
        valid_digit_string(s)
{
    cyclic_shift_remainder_helper(s, shift, m, 0, 0)
}

spec fn cyclic_shift_remainder_helper(s: Seq<char>, shift: int, m: int, pos: int, acc: int) -> int
    recommends 
        0 <= shift < s.len(),
        s.len() > 0,
        m >= 2,
        0 <= pos <= s.len(),
        0 <= acc < m,
        valid_digit_string(s)
    decreases (s.len() - pos) when 0 <= pos <= s.len()
{
    if pos == s.len() { 
        acc 
    } else {
        let idx = (shift + pos) % (s.len() as int);
        let digit = (s[idx] as int) - ('0' as int);
        let new_acc = (acc * 10 + digit) % m;
        cyclic_shift_remainder_helper(s, shift, m, pos + 1, new_acc)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}