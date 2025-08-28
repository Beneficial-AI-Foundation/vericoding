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
proof fn lemma_have_common_0_substring(str1: Seq<char>, str2: Seq<char>)
    ensures have_common_k_substring_pred(0, str1, str2)
{
    if str1.len() == 0 {
        assert(have_common_k_substring_pred(0, str1, str2)) by {
            assert(0 <= 0 <= str1.len() - 0);
            let empty_sub = str1.subrange(0, 0);
            assert(empty_sub.len() == 0);
            assert(is_substring_pred(empty_sub, str2)) by {
                assert(is_prefix_pred(empty_sub, str2.subrange(0, str2.len() as int))) by {
                    assert(empty_sub.len() <= str2.len());
                    assert(empty_sub == str2.subrange(0, empty_sub.len() as int));
                }
            }
        }
    } else {
        assert(have_common_k_substring_pred(0, str1, str2)) by {
            assert(0 <= 0 <= str1.len() - 0);
            let empty_sub = str1.subrange(0, 0);
            assert(empty_sub.len() == 0);
            assert(is_substring_pred(empty_sub, str2)) by {
                assert(is_prefix_pred(empty_sub, str2.subrange(0, str2.len() as int))) by {
                    assert(empty_sub.len() <= str2.len());
                    assert(empty_sub == str2.subrange(0, empty_sub.len() as int));
                }
            }
        }
    }
}

proof fn lemma_monotonicity(k1: nat, k2: nat, str1: Seq<char>, str2: Seq<char>)
    requires k1 <= k2, have_not_common_k_substring_pred(k1, str1, str2)
    ensures have_not_common_k_substring_pred(k2, str1, str2)
{
    if k2 <= str1.len() {
        assert(forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k2 && j1 == i1 + k2 ==> is_not_substring_pred(str1.subrange(i1, j1), str2)) by {
            assert(forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k1 && j1 == i1 + k1 ==> is_not_substring_pred(str1.subrange(i1, j1), str2));
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len(),
    ensures 
        forall|k: nat| #![auto] len < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
        have_common_k_substring_pred(len as nat, str1, str2),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        lemma_have_common_0_substring(str1, str2);
    }
    
    if str1.len() == 0nat {
        return 0;
    }
    
    let mut low: usize = 0;
    let mut high: usize = str1.len() as usize;
    
    while low < high
        invariant 
            0 <= low <= high <= str1.len(),
            have_common_k_substring_pred(low as nat, str1, str2),
            high < str1.len() ==> have_not_common_k_substring_pred((high + 1) as nat, str1, str2)
    {
        let mid = low + (high - low + 1) / 2;
        
        if have_common_k_substring(mid, str1, str2) {
            low = mid;
        } else {
            high = mid - 1;
            proof {
                if (high + 1) as nat < str1@len() {
                    lemma_monotonicity(mid as nat, (high + 1) as nat, str1, str2);
                }
            }
        }
    }
    
    low
}
// </vc-code>

fn main() {
}

}