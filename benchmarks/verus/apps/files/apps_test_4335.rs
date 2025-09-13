// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool {
    1 <= n <= 100 && s.len() == n && forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
}

spec fn is_concatenation_of_two_copies(s: Seq<char>) -> bool {
    s.len() % 2 == 0 && forall|i: int| 0 <= i < s.len()/2 ==> s[i] == s[s.len()/2 + i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: Seq<char>) -> (result: Seq<char>)
    requires valid_input(n, s)
    ensures result == seq!['Y', 'e', 's'] || result == seq!['N', 'o']
    ensures n % 2 != 0 ==> result == seq!['N', 'o']
    ensures n % 2 == 0 ==> (result == seq!['Y', 'e', 's'] <==> is_concatenation_of_two_copies(s))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}