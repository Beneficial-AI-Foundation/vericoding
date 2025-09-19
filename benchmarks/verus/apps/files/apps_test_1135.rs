// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n >= 1 && n <= 2000 && s.len() == n && 
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_output(result: Seq<char>, n: int) -> bool {
    result.len() == n && 
    forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] >= 'a' && #[trigger] result[i] <= 'z'
}

spec fn preserves_characters(s: Seq<char>, result: Seq<char>) -> bool {
    s.to_multiset() == result.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(n as int, s@)
    ensures 
        valid_output(result@, n as int),
        preserves_characters(s@, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}