// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    assume(false);
    true
}

spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}

spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && is_prefix_predicate(sub, str.subrange(i, str.len() as int)))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str),
{
    assume(false);
    true
}

spec fn have_common_k_substring_predicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && (exists|i: int| 0 <= i <= str1.len() - k && is_substring_predicate((str1.subrange(i, str1.len() as int)).subrange(0, k as int), str2))
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k <= usize::MAX,
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k as nat, str1, str2) == found,
{
    assume(false);
    true
}

spec fn max_common_substring_predicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool {
    forall|k: int| len < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    ensures 
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        max_common_substring_predicate(str1, str2, len as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}