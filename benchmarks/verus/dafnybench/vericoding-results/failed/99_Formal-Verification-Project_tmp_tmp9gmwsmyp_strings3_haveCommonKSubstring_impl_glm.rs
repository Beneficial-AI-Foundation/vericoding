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
fn is_prefix_exec(pre: &Vec<char>, str: &Vec<char>) -> (res: bool)
    ensures
        res <==> pre@.len() <= str@.len() && pre@ == str@.subrange(0, pre@.len() as int),
{
    if pre.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre@.subrange(0, i as int) == str@.subrange(0, i as int),
    {
        if pre[i] != str[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn is_substring_exec(sub: &Vec<char>, str: &Vec<char>) -> (res: bool)
    ensures
        res <==> exists|i: int| 0 <= i <= str@.len() - sub@.len() && sub@ == str@.subrange(i, i + sub@.len() as int),
{
    let sub_len = sub.len();
    let str_len = str.len();
    if sub_len == 0 {
        return true;
    }
    let mut i = 0;
    while i <= str_len - sub_len
        invariant
            0 <= i <= str_len - sub_len + 1,
            forall|j: int| 0 <= j < i ==> sub@ != str@.subrange(j, j + sub_len as int),
    {
        let slice: Vec<char> = str[i..i+sub_len].to_vec();
        if is_prefix_exec(&sub, &slice) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_substring_completeness(sub: Seq<char>, str: Seq<char>)
    ensures
        !is_substring_pred(sub, str) <==> is_not_substring_pred(sub, str),
{
    reveal(is_substring_pred);
    reveal(is_not_substring_pred);
    assert(!is_substring_pred(sub, str) <==> 
        forall|i: int| 0 <= i <= str.len() ==> !is_prefix_pred(sub, str.subrange(i, str.len() as int)));
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
    let k0 = k as usize;
    let str1_vec = str1.to_vec();
    let str2_vec = str2.to_vec();

    if k0 == 0 {
        return true;
    }

    if str1_vec.len() < k0 {
        return false;
    }

    let mut i = 0;
    while i <= str1_vec.len() - k0
        invariant
            0 <= i <= str1_vec.len() - k0 + 1,
            forall|j: int| 0 <= j < i ==> 
                is_not_substring_pred(str1@.subrange(j, j + k0 as int), str2@),
    {
        let substr: Vec<char> = str1_vec[i..i+k0].to_vec();
        if is_substring_exec(&substr, &str2_vec) {
            proof {
                lemma_substring_completeness(substr@, str2@);
            }
            return true;
        } else {
            proof {
                lemma_substring_completeness(substr@, str2@);
            }
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}

}