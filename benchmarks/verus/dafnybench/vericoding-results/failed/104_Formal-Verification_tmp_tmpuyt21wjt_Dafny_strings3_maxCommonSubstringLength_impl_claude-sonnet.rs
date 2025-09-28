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
proof fn empty_substring_always_exists(str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(0, str1, str2)
{
    assert(0 <= 0 && 0 + 0 <= str1.len());
    let sub = str1.subrange(0, 0);
    assert(sub.len() == 0);
    assert(is_prefix_pred(sub, str2.subrange(0, str2.len() as int)));
    assert(exists|i: int| #![auto] 0 <= i && i <= str2.len() && is_prefix_pred(sub, str2.subrange(i, str2.len() as int)));
}

proof fn k_greater_than_len_has_no_substring(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires k > str1.len()
    ensures !have_common_k_substring_pred(k, str1, str2)
{
    assert(forall|i1: int, j1: int| #![auto] 0 <= i1 && i1 + k <= str1.len() && j1 == i1 + k ==> false);
}

proof fn max_exists_lemma(str1: Seq<char>, str2: Seq<char>) -> (max_k: usize)
    requires str1.len() <= str2.len()
    ensures max_k <= str1.len()
    ensures have_common_k_substring_pred(max_k as nat, str1, str2)
    ensures forall|k: nat| #![auto] max_k < k && k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2)
{
    let mut k = str1.len();
    
    while k > 0
        invariant k <= str1.len()
        invariant forall|j: nat| #![auto] k < j && j <= str1.len() ==> !have_common_k_substring_pred(j, str1, str2)
        decreases k
    {
        if have_common_k_substring(k, str1, str2) {
            return k;
        }
        k = k - 1;
    }
    
    empty_substring_always_exists(str1, str2);
    0
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
    if str1.len() == 0 {
        proof {
            empty_substring_always_exists(str1, str2);
        }
        return 0;
    }
    
    let mut k = str1.len();
    
    while k > 0
        invariant k <= str1.len()
        invariant forall|j: nat| #![auto] k < j && j <= str1.len() ==> !have_common_k_substring_pred(j, str1, str2)
        decreases k
    {
        if have_common_k_substring(k, str1, str2) {
            return k;
        }
        k = k - 1;
    }
    
    proof {
        empty_substring_always_exists(str1, str2);
    }
    0
}
// </vc-code>

fn main() {
}

}