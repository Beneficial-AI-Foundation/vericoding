use vstd::prelude::*;

verus! {

// We spent 2h each on this assignment

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
    //ensures !res <==> is_not_substring_pred(sub@, s@) // This postcondition follows from the above lemma.
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

// <vc-helpers>
proof fn lemma_prefix_implies_substring(pre: Seq<char>, s: Seq<char>)
    requires is_prefix_pred(pre, s)
    ensures is_substring_pred(pre, s)
{
    assert(is_substring_pred(pre, s));
}

proof fn lemma_not_prefix_implies_not_substring_at_i(sub: Seq<char>, s: Seq<char>, i: int)
    requires 0 <= i <= s.len(), is_not_prefix_pred(sub, s.subrange(i, s.len() as int))
    ensures is_not_prefix_pred(sub, s.subrange(i, s.len() as int))
{
    assert(is_not_prefix_pred(sub, s.subrange(i, s.len() as int)));
}

spec fn seq_char_to_str(s: Seq<char>) -> Seq<char> {
    s
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn have_common_k_substring(k: nat, str1: &str, str2: &str) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k, str1@, str2@)
    //ensures !found <==> have_not_common_k_substring_pred(k, str1@, str2@) // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
fn have_common_k_substring(k: nat, str1: &str, str2: &str) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k, str1@, str2@)
{
    if k == 0 || str1.len() < k {
        return false;
    }

    let mut i: usize = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|j: int| 0 <= j < i ==> !is_substring_pred(str1@.subrange(j, j + k as int), str2@)
    {
        let substr = &str1[i..i + k];
        let res = is_substring(substr, str2);
        if res {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}