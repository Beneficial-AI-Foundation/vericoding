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

// <vc-helpers>
fn have_common_k_substring_complete(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    if k == 0 {
        return true;
    }
    
    if str1.len() < k {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str1.len() - k
        invariant
            0 <= i <= str1.len() - k + 1,
            forall|i0: int| #![auto] 0 <= i0 < i ==> is_not_substring_pred(str1.subrange(i0, i0 + k as int), str2),
    {
        let substring = str1.subrange(i as int, (i + k) as int);
        
        if is_substring_check(substring, str2) {
            assert(is_substring_pred(substring, str2));
            assert(have_common_k_substring_pred(k as nat, str1, str2));
            return true;
        }
        
        i += 1;
    }
    
    assert(forall|i0: int| #![auto] 0 <= i0 <= str1.len() - k ==> is_not_substring_pred(str1.subrange(i0, i0 + k as int), str2));
    false
}

fn is_substring_check(sub: Seq<char>, str: Seq<char>) -> (result: bool)
    ensures result <==> is_substring_pred(sub, str),
{
    if sub.len() == 0 {
        return true;
    }
    
    if str.len() < sub.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| #![auto] 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
    {
        if is_prefix_check(sub, str.subrange(i as int, str.len() as int)) {
            assert(is_prefix_pred(sub, str.subrange(i as int, str.len() as int)));
            assert(is_substring_pred(sub, str));
            return true;
        }
        i += 1;
    }
    
    false
}

fn is_prefix_check(pre: Seq<char>, str: Seq<char>) -> (result: bool)
    ensures result <==> is_prefix_pred(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            forall|j: int| #![auto] 0 <= j < i ==> pre@[j] == str@[j],
    {
        if pre@[i as int] != str@[i as int] {
            return false;
        }
        i += 1;
    }
    
    true
}
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
    if str1.len() == 0 {
        return 0;
    }
    
    let mut len: usize = str1.len();
    
    while len > 0
        invariant
            0 <= len <= str1.len(),
            forall|k: nat| #![auto] len < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
    {
        if have_common_k_substring_complete(len, str1, str2) {
            assert(have_common_k_substring_pred(len as nat, str1, str2));
            return len;
        }
        len = len - 1;
    }
    
    assert(have_common_k_substring_pred(0, str1, str2));
    0
}
// </vc-code>

fn main() {
}

}