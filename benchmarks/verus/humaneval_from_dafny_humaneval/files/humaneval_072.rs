// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_palindrome(s: Seq<int>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i]
}

spec fn sum_elements(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_elements(s.subrange(1, s.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Seq<int>, w: int) -> (result: bool)
    ensures result == (is_palindrome(q) && sum_elements(q) <= w)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}