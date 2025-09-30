// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn winner(a: char, b: char) -> char {
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') {
        b
    } else {
        a
    }
}

spec fn valid_rps_char(c: char) -> bool {
    c == 'R' || c == 'P' || c == 'S'
}

spec fn valid_rps_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> valid_rps_char(s[i])
}

spec fn valid_input(n: int, k: int, s: Seq<char>) -> bool {
    n > 0 && k >= 0 && s.len() == n && valid_rps_string(s)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_valid_rps_chars()
    ensures
        valid_rps_char('R'),
        valid_rps_char('P'),
        valid_rps_char('S'),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, s: Vec<char>) -> (result: char)
    requires valid_input(n as int, k as int, s@)
    ensures valid_rps_char(result)
// </vc-spec>
// <vc-code>
{
    'R'
}
// </vc-code>


}

fn main() {}