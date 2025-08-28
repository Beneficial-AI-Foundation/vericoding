use vstd::prelude::*;

verus! {

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
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
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        //!res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    false
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
proof fn lemma_subrange_len(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.subrange(start, end).len() == (end - start) as nat,
{
}

proof fn lemma_subrange_equal(s1: Seq<char>, s2: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s1.len(),
        0 <= start <= end <= s2.len(),
        s1.subrange(start, end) == s2.subrange(start, end),
    ensures
        forall|i: int| start <= i < end ==> s1@[i] == s2@[i],
{
}

proof fn lemma_prefix_implies_substring(sub: Seq<char>, str: Seq<char>, i: int)
    requires
        0 <= i <= str.len(),
        is_prefix_pred(sub, str.subrange(i, str.len() as int)),
    ensures
        is_substring_pred(sub, str),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        //!found <==> have_not_common_k_substring_pred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
    {
        if pre@[i] != str@[i] {
            return false;
        }
        i = i + 1;
    }
    true
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        !res <==> is_not_substring_pred(sub, str),
{
    if sub.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> !is_prefix_pred(sub, str.subrange(j, str.len() as int)),
    {
        if is_prefix(sub, str.subrange(i, str.len() as int)) {
            return true;
        }
        i = i + 1;
    }
    false
}

fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        !found <==> have_not_common_k_substring_pred(k, str1, str2),
{
    if k == 0 || k > str1.len() {
        return false;
    }
    let mut i = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|j: int| 0 <= j < i ==> !is_substring_pred(str1.subrange(j, j + k as int), str2),
    {
        let sub = str1.subrange(i, i + k as int);
        if is_substring(sub, str2) {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}

}