// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool 
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if str.len() < sub.len() {
        false
    } else {
        (str.subrange(0, sub.len() as int) == sub) || is_substring(sub, str.subrange(1, str.len() as int))
    }
}

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| #![auto] 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    assume(false);
    false
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len(),
    ensures 
        forall|k: nat| #![auto] len < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
        have_common_k_substring_pred(len as nat, str1, str2),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}