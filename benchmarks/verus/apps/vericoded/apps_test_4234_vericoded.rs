// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 0
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() % 2 == 0 && forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[2*i] != #[trigger] s[2*i+1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: (usize, Vec<char>))
    requires 
        valid_input(n as int, s@),
    ensures 
        result.0 >= 0,
        result.0 == s@.len() - result.1@.len(),
        is_good_string(result.1@),
        result.0 + result.1@.len() == s@.len(),
// </vc-spec>
// <vc-code>
{
    let removed: usize = s.len();
    let res: Vec<char> = Vec::new();
    (removed, res)
}
// </vc-code>


}

fn main() {}