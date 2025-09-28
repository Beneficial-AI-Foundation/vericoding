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
proof fn lemma_is_prefix_negation(pre: Seq<char>, str: Seq<char>)
    ensures
        !is_prefix_pred(pre, str) <==> is_not_prefix_pred(pre, str),
{
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_prefix_pred(pre, str),
        !res <==> is_not_prefix_pred(pre, str),
{
    let len = pre.len();
    if len > str.len() {
        return false;
    }
    pre == str.subrange(0, len as int)
}

proof fn lemma_is_substring_negation(sub: Seq<char>, str: Seq<char>)
    ensures
        !is_substring_pred(sub, str) <==> is_not_substring_pred(sub, str),
{
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        !res <==> is_not_substring_pred(sub, str),
{
    let sub_len = sub.len() as int;
    let str_len = str.len() as int;
    if sub_len > str_len {
        return false;
    }
    for i in 0..= (str_len - sub_len)
        invariant
            0 <= i <= str_len - sub_len + 1,
            forall |j: int| 0 <= j < i ==> !#[trigger] is_prefix_pred(sub, str.subrange(j, str_len)),
    {
        let candidate = str.subrange(i, str_len);
        if is_prefix(sub, candidate) {
            return true;
        }
    }
    false
}

proof fn lemma_have_common_k_substring_negation(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        !have_common_k_substring_pred(k, str1, str2) <==> have_not_common_k_substring_pred(k, str1, str2),
{
}
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        //!found <==> have_not_common_k_substring_pred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let k_int = k as int;
    let s1_len = str1.len() as int;
    if k_int > s1_len {
        return false;
    }
    for i in 0..= (s1_len - k_int)
        invariant
            k_int <= s1_len,
            0 <= i <= s1_len - k_int + 1,
            forall |j: int| 0 <= j < i ==> !#[trigger] is_substring_pred(str1.subrange(j, j + k_int), str2),
    {
        let sub = str1.subrange(i, i + k_int);
        assert(is_substring(sub, str2) <==> is_substring_pred(sub, str2));
        if is_substring(sub, str2) {
            return true;
        }
    }
    false
}
// </vc-code>

fn main() {}

}