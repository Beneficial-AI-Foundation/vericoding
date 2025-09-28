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
proof fn lemma_substring_equivalence(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring(sub, str) <==> is_substring_pred(sub, str),
        !is_substring(sub, str) <==> is_not_substring_pred(sub, str)
{
    reveal(is_substring_pred);
    reveal(is_not_substring_pred);
    reveal(is_prefix_pred);
    reveal(is_not_prefix_pred);
}

proof fn lemma_range_properties(s: Seq<char>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures
        s.subrange(i, j).len() == j - i,
        forall|k: int| 0 <= k < s.subrange(i, j).len() ==> s.subrange(i, j)[k] == s[i + k]
{
    assert(s.subrange(i, j).len() == j - i);
    assert(forall|k: int| 0 <= k < s.subrange(i, j).len() ==> s.subrange(i, j)[k] == s[i + k]);
}

fn have_common_k_substring_impl(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    if k == 0 {
        assert(have_common_k_substring_pred(0, str1, str2));
        return true;
    }
    if k > str1.len() {
        assert(!have_common_k_substring_pred(k as nat, str1, str2));
        return false;
    }
    
    let mut i = 0;
    while i < str1.len() - k + 1
        invariant 0 <= i <= str1.len() - k + 1
        invariant forall|j: int| 0 <= j < i ==> !is_substring_pred(str1.subrange(j, j + k), str2)
    {
        let substring = str1.subrange(i, i + k);
        lemma_range_properties(str1, i, i + k);
        if is_substring(substring, str2) {
            lemma_substring_equivalence(substring, str2);
            return true;
        }
        i = i + 1;
    }
    assert(!have_common_k_substring_pred(k as nat, str1, str2));
    false
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
    let mut low = 0;
    let mut high = str1.len() + 1;
    
    while low < high
        invariant 0 <= low <= high <= str1.len() + 1
        invariant forall|k: nat| #![auto] high <= k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2)
        invariant forall|k: nat| #![auto] 0 <= k < low ==> have_common_k_substring_pred(k, str1, str2)
    {
        let mid = (low + high) / 2;
        if have_common_k_substring_impl(mid, str1, str2) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    assert(forall|k: nat| #![auto] low < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2));
    assert(low <= str1.len());
    if low > 0 {
        have_common_k_substring_impl(low - 1, str1, str2);
    }
    
    if low == 0 {
        0
    } else {
        low - 1
    }
}
// </vc-code>

fn main() {
}

}