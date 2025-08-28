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
proof fn lemma_empty_substring_common(str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(0, str1, str2)
{
    assert(str1.subrange(0, 0) == Seq::<char>::empty());
    assert(is_prefix_pred(Seq::<char>::empty(), str2.subrange(0, str2.len() as int)));
    assert(is_substring_pred(str1.subrange(0, 0), str2));
}

proof fn lemma_k_greater_than_len_no_common(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires k > str1.len()
    ensures !have_common_k_substring_pred(k, str1, str2)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures (forall|k: nat| #![auto] len < k && k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2))
        && have_common_k_substring_pred(len as nat, str1, str2)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if str1.len() == 0 {
        proof { lemma_empty_substring_common(str1, str2); }
        return 0;
    }
    
    let mut max_len: usize = 0;
    proof { lemma_empty_substring_common(str1, str2); }
    
    let mut k: usize = 1;
    while k <= str1.len()
        invariant 0 <= max_len <= k <= str1.len()
        invariant have_common_k_substring_pred(max_len as nat, str1, str2)
        invariant forall|j: nat| #![auto] max_len < j && j < k ==> !have_common_k_substring_pred(j, str1, str2)
    {
        let found = have_common_k_substring(k, str1, str2);
        if found {
            max_len = k;
        }
        k = k + 1;
    }
    
    max_len
}
// </vc-code>

fn main() {
}

}