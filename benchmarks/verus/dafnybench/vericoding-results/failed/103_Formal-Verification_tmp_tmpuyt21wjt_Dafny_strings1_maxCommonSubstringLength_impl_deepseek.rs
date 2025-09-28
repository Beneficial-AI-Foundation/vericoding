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
spec fn is_not_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
    !is_prefix_predicate(pre, str)
}

proof fn is_prefix_equivalence(pre: Seq<char>, str: Seq<char>)
    ensures 
        is_prefix_predicate(pre, str) == !is_not_prefix_predicate(pre, str)
{
}

proof fn is_substring_non_empty_witness(sub: Seq<char>, str: Seq<char>, i: int)
    requires 
        is_substring_predicate(sub, str),
        0 <= i <= str.len() - sub.len(),
        is_prefix_predicate(sub, str.subrange(i, str.len() as int))
    ensures 
        is_substring_predicate(sub, str)
{
}

proof fn have_common_k_substring_witness_k(k: nat, str1: Seq<char>, str2: Seq<char>, i: int)
    requires 
        have_common_k_substring_predicate(k, str1, str2),
        0 <= i <= str1.len() - (k as int),
        is_substring_predicate((str1.subrange(i, str1.len() as int)).subrange(0, k as int), str2)
    ensures 
        have_common_k_substring_predicate(k, str1, str2)
{
}

proof fn max_common_substring_none_exists(str1: Seq<char>, str2: Seq<char>, len: nat, k: nat)
    requires 
        max_common_substring_predicate(str1, str2, len),
        len < k <= str1.len()
    ensures 
        !have_common_k_substring_predicate(k, str1, str2)
{
}

proof fn max_common_substring_zero(str1: Seq<char>, str2: Seq<char>)
    ensures max_common_substring_predicate(str1, str2, 0)
{
    assert forall|k: int| 0 < k <= str1.len() implies !have_common_k_substring_predicate(k as nat, str1, str2) by {
    }
}

proof fn max_common_substring_predicate_implies(str1: Seq<char>, str2: Seq<char>, len: nat, k: nat)
    requires
        max_common_substring_predicate(str1, str2, len),
        len < k <= str1.len()
    ensures
        !have_common_k_substring_predicate(k, str1, str2)
{
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
    let mut max_len: usize = 0;
    
    proof {
        max_common_substring_zero(str1, str2);
        assert(max_common_substring_predicate(str1, str2, 0));
    }
    
    let mut k: usize = 1;
    let str1_len_usize: usize = str1.len() as usize;
    let str2_len_usize: usize = str2.len() as usize;
    while k <= str1_len_usize && k <= str2_len_usize
        invariant
            0 <= k <= str1.len() + 1,
            max_len <= str1.len(),
            max_len <= str2.len(),
            max_common_substring_predicate(str1, str2, max_len as nat),
            forall|i: nat| i < k as nat ==> #[trigger] have_common_k_substring_predicate(i, str1, str2) == (i <= max_len as nat),
    {
        let found = have_common_k_substring(k, str1, str2);
        if found {
            max_len = k;
            proof {
                assert(have_common_k_substring_predicate(k as nat, str1, str2));
                assert forall|i: nat| k as nat < i <= str1.len() implies !have_common_k_substring_predicate(i, str1, str2) by {
                    assert(max_common_substring_predicate(str1, str2, max_len as nat));
                    max_common_substring_none_exists(str1, str2, max_len as nat, i);
                }
            }
        } else {
            proof {
                assert(!have_common_k_substring_predicate(k as nat, str1, str2));
            }
        }
        k = k + 1;
    }
    
    proof {
        assert forall|i: nat| i > max_len as nat && i <= str1.len() implies !have_common_k_substring_predicate(i, str1, str2) by {
            assert(max_common_substring_predicate(str1, str2, max_len as nat));
            max_common_substring_none_exists(str1, str2, max_len as nat, i);
        }
    }
    
    max_len
}
// </vc-code>

fn main() {}

}