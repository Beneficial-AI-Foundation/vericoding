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
fn chk_is_substring(sub: Seq<char>, str: Seq<char>) -> (b: bool)
    decreases str.len()
    ensures b <==> is_substring(sub, str)
{
    if sub.len() == 0 {
        return true;
    } else if str.len() < sub.len() {
        return false;
    } else {
        if str.subrange(0, sub.len() as int) == sub {
            return true;
        } else {
            return chk_is_substring(sub, str.subrange(1, str.len() as int));
        }
    }
}

fn check_common_k(k: nat, str1: Seq<char>, str2: Seq<char>) -> (b: bool)
    requires k <= str1.len()
    ensures b <==> have_common_k_substring_pred(k, str1, str2)
{
    let mut i1: int = 0;
    while i1 <= str1.len() - k
        invariant 0 <= i1 <= str1.len() - k + 1
    {
        let sub = str1.subrange(i1, i1 + k as int);
        let is = chk_is_substring(sub, str2);
        if is {
            proof {
                assert(have_common_k_substring_pred(k, str1, str2));
            }
            return true;
        }
        i1 += 1;
    }
    proof {
        assert(forall|i1: int| #![auto] 0 <= i1 <= str1.len() - k ==> !is_substring_pred(str1.subrange(i1, i1 + k), str2));
    }
    return false;
}
// </vc-helpers>
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
    let mut k: usize = str1.len() as usize;
    let mut found: bool = false;
    let mut result: usize = 0;
    while k > 0
        invariant 0 <= k <= str1.len(),
        invariant !found ==> result == 0,
        invariant forall|kk: nat| #![auto] (!found && k < kk <= str1.len()) ==> !have_common_k_substring_pred(kk, str1, str2)
    {
        let has = check_common_k(k as nat, str1, str2);
        if has {
            found = true;
            result = k;
            break;
        } else {
            proof {
                assert(!have_common_k_substring_pred(k as nat, str1, str2));
            }
            k -= 1;
        }
    }
    if !found {
        result = 0;
    }
    proof {
        if found {
            assert(have_common_k_substring_pred(result as nat, str1, str2));
            assert(forall|kk: nat| #![auto] result < kk <= str1.len() ==> !have_common_k_substring_pred(kk, str1, str2));
        } else {
            assert(result == 0);
            assert(forall|kk: nat| #![auto] 0 < kk <= str1.len() ==> !have_common_k_substring_pred(kk, str1, str2));
            assert(have_common_k_substring_pred(0, str1, str2));
        }
    }
    result
}
// </vc-code>
// </vc-code>

fn main() {
}

}