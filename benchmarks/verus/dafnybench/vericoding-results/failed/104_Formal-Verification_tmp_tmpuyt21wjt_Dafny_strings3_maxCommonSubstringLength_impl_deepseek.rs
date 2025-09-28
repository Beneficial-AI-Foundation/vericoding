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
proof fn lemma_substring_pred_implies_exists_index(sub: Seq<char>, str: Seq<char>)
    requires
        is_substring_pred(sub, str),
    ensures
        exists|i: int| 0 <= i && i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int)),
{
}

proof fn lemma_not_substring_pred_implies_forall_index(sub: Seq<char>, str: Seq<char>)
    requires
        is_not_substring_pred(sub, str),
    ensures
        forall|i: int| 0 <= i && i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int)),
{
}

proof fn lemma_have_common_k_substring_pred_implies_exists(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        have_common_k_substring_pred(k, str1, str2),
    ensures
        exists|i1: int, j1: int| 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2),
{
}

proof fn lemma_have_not_common_k_substring_pred_implies_forall(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        have_not_common_k_substring_pred(k, str1, str2),
    ensures
        forall|i1: int, j1: int| 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2),
{
}

proof fn lemma_is_prefix_pred_transitive(pre: Seq<char>, mid: Seq<char>, str: Seq<char>)
    requires
        is_prefix_pred(pre, mid),
        is_prefix_pred(mid, str),
    ensures
        is_prefix_pred(pre, str),
{
}

proof fn lemma_is_not_prefix_pred_contrapositive(pre: Seq<char>, str: Seq<char>)
    requires
        is_not_prefix_pred(pre, str),
    ensures
        pre.len() > str.len() || pre != str.subrange(0, pre.len() as int),
{
}

proof fn lemma_subrange_len(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        s.subrange(i, j).len() == j - i,
{
}

proof fn lemma_subrange_subrange(s: Seq<char>, i: int, j: int, k: int, l: int)
    requires
        0 <= i <= k <= l <= j <= s.len(),
    ensures
        s.subrange(i, j).subrange(k - i, l - i) == s.subrange(k, l),
{
}

proof fn lemma_prefix_of_subrange_is_prefix_of_original(pre: Seq<char>, s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        is_prefix_pred(pre, s.subrange(i, s.len() as int)),
    ensures
        exists|j: int| i <= j <= s.len() && is_prefix_pred(pre, s.subrange(j, s.len() as int)),
{
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
    let str1_len: usize = str1.len() as usize;
    let str2_len: usize = str2.len() as usize;
    
    let mut low: usize = 0;
    let mut high: usize = str1_len;
    let mut result: usize = 0;
    
    while low <= high
        invariant
            low <= high <= str1_len + 1,
            forall|k: nat| #![auto] (high as nat) < k && k <= (str1_len as nat) ==> !have_common_k_substring_pred(k, str1, str2),
            have_common_k_substring_pred(result as nat, str1, str2),
    {
        let mid = low + (high - low) / 2;
        proof {
            lemma_have_common_k_substring_pred_implies_exists(mid as nat, str1, str2);
            lemma_have_not_common_k_substring_pred_implies_forall(mid as nat, str1, str2);
        }
        
        let found = have_common_k_substring(mid, str1, str2);
        
        if found {
            result = mid;
            low = mid + 1;
        } else {
            if mid == 0 {
                high = mid;
            } else {
                high = mid - 1;
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}