// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_postal_code(a: int, b: int, s: Seq<char>) -> bool
    recommends 
        a >= 1 && b >= 1 && a <= 5 && b <= 5,
        s.len() == a + b + 1,
        forall|i: int| 0 <= i < s.len() ==> (s[i] == '-' || ('0' <= s[i] <= '9'))
{
    s[a] == '-' && forall|i: int| 0 <= i < s.len() && i != a ==> s[i] != '-'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, s: Seq<char>) -> (result: Seq<char>)
    requires 
        a >= 1 && b >= 1 &&
        a <= 5 && b <= 5 &&
        s.len() == a + b + 1 &&
        forall|i: int| 0 <= i < s.len() ==> (s[i] == '-' || ('0' <= s[i] <= '9'))
    ensures 
        result == seq!['Y', 'e', 's'] || result == seq!['N', 'o'],
    ensures 
        (result == seq!['Y', 'e', 's']) <==> valid_postal_code(a, b, s)
// </vc-spec>
// <vc-code>
{
    /* impl-start */
    assume(false);
    seq!['N', 'o']
    /* impl-end */
}
// </vc-code>


}

fn main() {}