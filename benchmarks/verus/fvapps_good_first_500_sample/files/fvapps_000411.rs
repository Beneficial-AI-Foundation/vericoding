// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn substring_at(s: Seq<char>, i: int) -> Seq<char> {
    if 0 <= i <= s.len() {
        s.subrange(i, s.len() as int)
    } else {
        seq![]
    }
}

spec fn string_ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    s.len() >= suffix.len() && s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
}

spec fn is_lexicographically_ge(s1: Seq<char>, s2: Seq<char>) -> bool {
    if s1.len() == 0 && s2.len() == 0 {
        true
    } else if s1.len() == 0 {
        false
    } else if s2.len() == 0 {
        true
    } else {
        s1[0] > s2[0] || (s1[0] == s2[0] && is_lexicographically_ge(s1.skip(1), s2.skip(1)))
    }
}

fn last_substring(s: &str) -> (result: String)
    requires s.len() > 0,
    ensures
        result.len() > 0,
        string_ends_with(s@, result@),
        forall|i: int| 0 <= i < s.len() ==> is_lexicographically_ge(result@, substring_at(s@, i)),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #eval last_substring "abab"
    // #eval last_substring "leetcode"
    // #eval last_substring "zzz"
}