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
// Helper lemma to show that if no common substring of length k exists,
// then no common substring of any length > k exists
proof fn no_longer_substring_implies_no_shorter(str1: Seq<char>, str2: Seq<char>, k: nat, j: nat)
    requires
        j > k,
        !have_common_k_substring_predicate(j, str1, str2),
    ensures
        !have_common_k_substring_predicate(j, str1, str2),
{
    // This is trivially true by the requirement
}

// Helper to establish the max_common_substring_predicate
proof fn establish_max_predicate(str1: Seq<char>, str2: Seq<char>, found_len: nat)
    requires
        found_len <= str1.len(),
        found_len <= str2.len(),
        forall|k: nat| found_len < k <= str1.len().min(str2.len()) ==> !have_common_k_substring_predicate(k, str1, str2),
    ensures
        max_common_substring_predicate(str1, str2, found_len),
{
    assert forall|k: int| found_len < k <= str1.len() implies !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2) by {
        if k <= str2.len() {
            // Covered by our requirement
            assert(!have_common_k_substring_predicate(k as nat, str1, str2));
        } else {
            // k > str2.len(), so no substring of length k can exist
            assert(!(str1.len() >= k && str2.len() >= k));
            assert(!have_common_k_substring_predicate(k as nat, str1, str2));
        }
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
    let str1_len = str1.len();
    let str2_len = str2.len();
    
    // Compute minimum length
    let min_len: usize = if str1_len <= str2_len { 
        str1_len
    } else { 
        str2_len
    };
    
    // Start from the maximum possible length and work down
    let mut k = min_len;
    
    while k > 0
        invariant
            0 <= k <= min_len,
            min_len <= str1.len(),
            min_len <= str2.len(),
            forall|j: nat| k < j <= min_len ==> !have_common_k_substring_predicate(j, str1, str2),
    {
        let found = have_common_k_substring(k, str1, str2);
        if found {
            // We found a common substring of length k
            proof {
                establish_max_predicate(str1, str2, k as nat);
            }
            return k;
        }
        k = k - 1;
    }
    
    // No common substring found
    proof {
        assert forall|j: nat| 0 < j <= min_len implies !have_common_k_substring_predicate(j, str1, str2) by {
            assert(!have_common_k_substring_predicate(j, str1, str2));
        }
        establish_max_predicate(str1, str2, 0);
    }
    
    0
}
// </vc-code>

fn main() {}

}