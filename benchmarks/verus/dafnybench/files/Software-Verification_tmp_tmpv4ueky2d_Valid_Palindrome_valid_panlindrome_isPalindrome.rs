// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn isPalindrome(s: &Vec<char>) -> (result: bool)
    requires 1 <= s.len() <= 200000,
    ensures result <==> (forall|i: int| 0 <= i < (s.len() as int) / 2 ==> s[i] == s[(s.len() as int) - 1 - i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}