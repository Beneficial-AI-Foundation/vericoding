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
proof fn lemma_no_larger_common_substring(k: nat, max_k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        max_k < k <= str1.len(),
        have_not_common_k_substring_pred(max_k as nat, str1, str2),
    ensures
        have_not_common_k_substring_pred(k as nat, str1, str2),
{
    assert forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k 
        implies is_not_substring_pred(str1.subrange(i1, j1), str2) by {
        if 0 <= i1 <= str1.len() - k && j1 == i1 + k {
            // If there's no common substring of length max_k starting at position i1,
            // then there's definitely no common substring of length k > max_k starting at i1
            // This is because a longer substring would contain the shorter one
            assert(is_not_substring_pred(str1.subrange(i1, j1), str2));
        }
    }
}

proof fn lemma_empty_substring_always_exists(str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(0 as nat, str1, str2)
{
    // Empty substring always exists
    assert(0 <= 0 <= str1.len() - 0);
    assert(str1.subrange(0, 0).len() == 0);
    assert(is_prefix_pred(str1.subrange(0, 0), str2.subrange(0, str2.len() as int)));
    assert(is_substring_pred(str1.subrange(0, 0), str2));
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
    let mut k: usize = str1.len() as usize;
    
    while k > 0
        invariant
            k <= str1.len(),
            forall|j: nat| #![auto] k < j <= str1.len() ==> have_not_common_k_substring_pred(j, str1, str2),
    {
        if have_common_k_substring(k, str1, str2) {
            // Found a common substring of length k
            return k;
        }
        
        // No common substring of length k, so definitely none of length > k
        assert(have_not_common_k_substring_pred(k as nat, str1, str2));
        
        k = k - 1;
    }
    
    // k == 0, empty substring always exists
    proof {
        lemma_empty_substring_always_exists(str1, str2);
    }
    
    0
}
// </vc-code>

fn main() {
}

}