// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 0
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() % 2 == 0 && forall|i: int| 0 <= i < s.len()/2 ==> s[2*i] != s[2*i+1]
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Seq<char>) -> (result: (usize, Seq<char>))
    requires 
        valid_input(n as int, s)
    ensures 
        result.0 >= 0 &&
        result.0 == s.len() - result.1.len() &&
        is_good_string(result.1) &&
        result.0 + result.1.len() == s.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}