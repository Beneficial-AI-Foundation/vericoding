// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, s: Seq<char>) -> bool {
    pre.len() <= s.len() && 
    pre == s.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, s: Seq<char>) -> bool {
    pre.len() > s.len() || 
    pre != s.subrange(0, pre.len() as int)
}

fn is_prefix(pre: &str, s: &str) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre@, s@),
        res <==> is_prefix_pred(pre@, s@)
{
    assume(false);
    true
}

spec fn is_substring_pred(sub: Seq<char>, s: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= s.len() && is_prefix_pred(sub, s.subrange(i, s.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, s: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= s.len() ==> is_not_prefix_pred(sub, s.subrange(i, s.len() as int))
}

fn is_substring(sub: &str, s: &str) -> (res: bool)
    ensures res <==> is_substring_pred(sub@, s@)

{
    assume(false);
    true
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k && 
        is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k ==> 
        is_not_substring_pred(str1.subrange(i1, j1), str2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: &str, str2: &str) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k, str1@, str2@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}