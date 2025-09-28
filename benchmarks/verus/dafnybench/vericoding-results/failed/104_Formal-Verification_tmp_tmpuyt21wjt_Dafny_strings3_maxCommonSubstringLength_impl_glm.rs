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
fn have_common_k_substring_impl(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1, str2)
{
    if k == 0 || k > str1.len() {
        if k == 0 {
            assert(have_common_k_substring_pred(0, str1, str2));
            true
        } else {
            assert(!have_common_k_substring_pred(k as nat, str1, str2));
            false
        }
    } else {
        let mut i = 0;
        let mut found = false;
        while i <= str1.len() - k
            invariant 0 <= i <= str1.len() - k + 1
            invariant found <==> exists|i1: int| 0 <= i1 < i && is_substring_pred(str1.subrange(i1, i1 + k), str2)
        {
            let substring = str1.subrange(i, i + k);
            if is_substring_pred(substring, str2) {
                found = true;
                i = str1.len() - k + 1;
            } else {
                i += 1;
            }
        }
        found
    }
}

proof fn lemma_common_k_implies_common_smaller(k: nat, smaller: nat, str1: Seq<char>, str2: Seq<char>)
    requires smaller <= k
    requires have_common_k_substring_pred(k, str1, str2)
    ensures have_common_k_substring_pred(smaller, str1, str2)
{
    if smaller == 0 {
        assert(have_common_k_substring_pred(0, str1, str2));
    } else if smaller > str1.len() {
        assert(!have_common_k_substring_pred(smaller, str1, str2));
    } else {
        let (i1, j1) = choose|i1: int, j1: int| 
            #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2);
        
        let matching_index = choose|i: int| 
            0 <= i && i <= str2.len() && is_prefix_pred(str1.subrange(i1, j1), str2.subrange(i, str2.len() as int));
        
        assert(is_prefix_pred(str1.subrange(i1, i1 + smaller as int), str2.subrange(match
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len()
    ensures (forall|k: nat| #![auto] len < k && k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2))
        && have_common_k_substring_pred(len as nat, str1, str2)
// </vc-spec>
// <vc-code>
fn have_common_k_substring_impl(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures found <==> have_common_k_substring_pred(k as nat, str1, str2)
{
    if k == 0 || k > str1.len() {
        if k == 0 {
            assert(have_common_k_substring_pred(0, str1, str2));
            true
        } else {
            assert(!have_common_k_substring_pred(k as nat, str1, str2));
            false
        }
    } else {
        let mut i = 0;
        let mut found = false;
        while i <= str1.len() - k
            invariant 0 <= i <= str1.len() - k + 1
            invariant found <==> exists|i1: int| 0 <= i1 < i && is_substring_pred(str1.subrange(i1, i1 + k), str2)
        {
            let substring = str1.subrange(i, i + k);
            if is_substring_pred(substring, str2) {
                found = true;
                i = str1.len() - k + 1;
            } else {
                i += 1;
            }
        }
        found
    }
}

proof fn lemma_common_k_implies_common_smaller(k: nat, smaller: nat, str1: Seq<char>, str2: Seq<char>)
    requires smaller <= k
    requires have_common_k_substring_pred(k, str1, str2)
    ensures have_common_k_substring_pred(smaller, str1, str2)
{
    if smaller == 0 {
        assert(have_common_k_substring_pred(0, str1, str2));
    } else if smaller > str1.len() {
        assert(!have_common_k_substring_pred(smaller, str1, str2));
    } else {
        let (i1, j1) = choose|i1: int, j1: int| 
            #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2);
        
        let matching_index = choose|i: int| 
            0 <= i && i <= str2.len() && is_prefix_pred(str1.subrange(i1, j1), str2.subrange(i, str2.len() as int));
        
        assert(is_prefix_pred(str1.subrange(i1, i1 + smaller as int), str2.subrange(match
// </vc-code>

fn main() {
}

}