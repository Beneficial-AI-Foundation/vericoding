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

// <vc-helpers>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    if pre.len() > 0 && str.len() >= pre.len() {
        let mut i = 0;
        while i < pre.len()
            invariant 0 <= i <= pre.len(),
            invariant forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
        {
            if pre@[i] != str@[i] {
                return false;
            }
            i += 1;
        }
        true
    } else {
        pre.len() == 0
    }
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str),
{
    if sub.len() == 0 {
        true
    } else if str.len() < sub.len() {
        false
    } else {
        let mut i = 0;
        let mut found = false;
        while i <= str.len() - sub.len()
            invariant 0 <= i <= str.len() - sub.len() + 1,
            invariant found ==> exists|j: int| 0 <= j < i && is_prefix_predicate(sub, str.subrange(j, str.len() as int)),
            invariant !found ==> forall|j: int| 0 <= j < i ==> !is_prefix_predicate(sub, str.subrange(j, str.len() as int)),
        {
            if is_prefix(sub, str.subrange(i, str.len() as int)) {
                found = true;
                break;
            }
            i += 1;
        }
        found
    }
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k <= usize::MAX,
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k as nat, str1, str2) == found,
{
    if str1.len() < k || str2.len() < k {
        false
    } else {
        let mut i = 0;
        let mut found = false;
        while i <= str1.len() - k
            invariant 0 <= i <= str1.len() - k + 1,
            invariant found ==> exists|j: int| 0 <= j < i && is_substring_predicate(str1.subrange(j, j + k as int), str2),
            invariant !found ==> forall|j: int| 0 <= j < i ==> !is_substring_predicate(str1.subrange(j, j + k as int), str2),
        {
            proof {
                assert str1.subrange(i, i + k as int) == str1.subrange(i, str1.len() as int).subrange(0, k as int);
            }
            if is_substring(str1.subrange(i, i + k as int), str2) {
                found = true;
                break;
            }
            i += 1;
        }
        found
    }
}
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
    let mut low = 0;
    let mut high = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    let mut result = 0;
    
    while low <= high
        invariant 0 <= low <= high + 1,
        invariant high <= str1.len() && high <= str2.len(),
        invariant result == high,
        invariant max_common_substring_predicate(str1, str2, result as nat),
    {
        let mid = (low + high) / 2;
        if have_common_k_substring(mid, str1, str2) {
            proof {
                assert forall|k: int| result < k <= mid ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2) by {
                    assert high < k;
                }
            }
            low = mid + 1;
            result = mid;
        } else {
            proof {
                assert forall|k: int| mid < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2) by {
                    assert have_common_k_substring_predicate(mid as nat, str1, str2) == false;
                }
            }
            high = mid - 1;
        }
    }
    result
}
// </vc-code>

fn main() {}

}