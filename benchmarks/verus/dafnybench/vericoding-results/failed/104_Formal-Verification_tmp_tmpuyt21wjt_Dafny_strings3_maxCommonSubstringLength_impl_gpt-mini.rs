use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool 
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if sub.len() > str.len() {
        false  
    } else {
        sub == str.subrange(0, sub.len() as int) || is_substring(sub, str.subrange(1, str.len() as int))
    }
}

// We spent 2h each on this assignment

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| #![auto] 0 <= i && i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i && i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}


spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1, str2)
    //ensures !found <==> have_not_common_k_substring_pred(k, str1, str2) // This postcondition follows from the above lemma.
{
    assume(false);
    false
}

// <vc-helpers>
fn is_substring_bool(sub: Seq<char>, str: Seq<char>) -> (b: bool)
    ensures b <==> is_substring_pred(sub, str)
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if sub.len() > str.len() {
        false
    } else {
        let k: int = sub.len();
        if sub == str.subrange(0, k) {
            true
        } else {
            is_substring_bool(sub, str.subrange(1, str.len() as int))
        }
    }
}

fn have_common_k_substring_impl(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1, str2)
{
    let kn: int = k as int;
    if kn > str1.len() {
        false
    } else {
        let limit: int = str1.len() - kn;
        let mut i1: int = 0;
        while i1 <= limit
            invariant 0 <= i1 && i1 <= limit + 1
            invariant forall|j: int| 0 <= j && j < i1 ==> !is_substring_pred(str1.subrange(j, j + kn), str2)
            decreases limit + 1 - i1
        {
            let j1: int = i1 + kn;
            let sub: Seq<char> = str1.subrange(i1, j1);
            let b: bool = is_substring_bool(sub, str2);
            if b {
                return true;
            } else {
                i1 = i1 + 1;
            }
        }
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures (forall|k: nat| #![auto] len < k && k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2))
        && have_common_k_substring_pred(len as nat, str1, str2)
// </vc-spec>
// <vc-code>
{
    let n: int = str1.len();
    let mut k: int = 0;
    let mut best: int = 0;
    while k <= n
        invariant 0 <= k && k <= n + 1
        invariant 0 <= best && best <= n
        invariant have_common_k_substring_pred(best as nat, str1, str2)
        invariant forall|t: int| 0 <= t && t < k ==> (have_common_k_substring_pred(t as nat, str1, str2) ==> t <= best)
        decreases n + 1 - k
    {
        let b: bool = have_common_k_substring_impl(k as usize, str1, str2);
        if b {
            best = k;
        }
        k = k + 1;
    }
    // after loop k == n+1
    // show that for all t with best < t <= n, there is no common substring of length t
    assert(k == n + 1);
    assert(forall|t: int| best < t && t <= n ==> !have_common_k_substring_pred(t as nat, str1, str2));
    best as usize
}
// </vc-code>

fn main() {
}

}