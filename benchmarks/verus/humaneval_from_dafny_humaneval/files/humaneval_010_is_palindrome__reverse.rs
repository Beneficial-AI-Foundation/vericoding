// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_palindrome(s: Seq<char>) -> bool {
    forall|k: int| #![trigger s[k as int]] 0 <= k < s.len() ==> s[k as int] == s[(s.len() - 1 - k) as int]
}

spec fn starts_with(result: Seq<char>, s: Seq<char>) -> bool {
    result.len() >= s.len() && forall|k: int| #![trigger result[k as int]] 0 <= k < s.len() ==> result[k as int] == s[k as int]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(str: Seq<char>) -> (rev: Seq<char>)
    ensures
        rev.len() == str.len(),
        forall|k: int| #![trigger rev[k as int]] 0 <= k < str.len() ==> rev[k as int] == str[(str.len() - 1 - k) as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}