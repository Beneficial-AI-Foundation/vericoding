use vstd::prelude::*;

verus! {

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
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
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        //!res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    false
}


spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k && 
        is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 
        0 <= i1 <= str1.len() - k && 
        j1 == i1 + k ==> 
        is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_is_not_prefix_equiv(pre: Seq<char>, str: Seq<char>)
    ensures is_not_prefix_pred(pre, str) == !is_prefix_pred(pre, str)
{
}

proof fn lemma_is_not_substring_equiv(sub: Seq<char>, str: Seq<char>)
    ensures is_not_substring_pred(sub, str) == !is_substring_pred(sub, str)
{
}

proof fn lemma_have_not_common_k_substring_equiv(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures have_not_common_k_substring_pred(k, str1, str2) == !have_common_k_substring_pred(k, str1, str2)
{
}
// </vc-helpers>

// <vc-spec>
fn have_common_k_substring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k, str1, str2),
        //!found <==> have_not_common_k_substring_pred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        proof {
            assert(exists|i1: int, j1: int| 
                0 <= i1 <= str1.len() - k && 
                j1 == i1 + k && 
                is_substring_pred(str1.subrange(i1, j1), str2)) by {
                assert(0 <= 0 <= str1.len() - 0);
                assert(str1.subrange(0, 0).len() == 0);
                assert(is_prefix_pred(str1.subrange(0, 0), str2.subrange(0, str2.len() as int)));
                assert(is_substring_pred(str1.subrange(0, 0), str2));
            }
        }
        return true;
    }
    
    if str1.len() < k {
        proof {
            assert(forall|i1: int, j1: int| 
                0 <= i1 <= str1.len() - k && 
                j1 == i1 + k ==> 
                is_not_substring_pred(str1.subrange(i1, j1), str2)) by {
                assert(str1.len() < k);
                assert(forall|i1: int| 0 <= i1 <= str1.len() - k ==> false);
            }
            assert(have_not_common_k_substring_pred(k, str1, str2));
            lemma_have_not_common_k_substring_equiv(k, str1, str2);
        }
        return false;
    }
    
    let mut i1: usize = 0;
    while i1 <= str1.len() - k
        invariant
            0 <= i1 <= str1.len() - k + 1,
            forall|idx: int| 0 <= idx < i1 ==> is_not_substring_pred(str1.subrange(idx, idx + k as int), str2),
    {
        let substring = str1.subrange(i1 as int, i1 as int + k as int);
        let found_substring = is_substring(substring, str2);
        
        if found_substring {
            proof {
                assert(is_substring_pred(substring, str2));
                assert(0 <= i1 as int <= str1.len() - k);
                assert((i1 as int + k as int) == i1 as int + k);
                assert(exists|i1_wit: int, j1_wit: int| 
                    0 <= i1_wit <= str1.len() - k && 
                    j1_wit == i1_wit + k && 
                    is_substring_pred(str1.subrange(i1_wit, j1_wit), str2)) by {
                    assert(str1.subrange(i1 as int, i1 as int + k as int) == substring);
                }
                assert(have_common_k_substring_pred(k, str1, str2));
            }
            return true;
        }
        
        assert(!is_substring_pred(substring, str2));
        proof {
            lemma_is_not_substring_equiv(substring, str2);
        }
        assert(is_not_substring_pred(substring, str2));
        i1 += 1;
    }
    
    proof {
        assert(i1 == str1.len() - k + 1);
        assert(forall|idx: int| 0 <= idx <= str1.len() - k ==> is_not_substring_pred(str1.subrange(idx, idx + k as int), str2)) by {
            assert(forall|idx: int| 0 <= idx < i1 ==> is_not_substring_pred(str1.subrange(idx, idx + k as int), str2));
            assert(i1 > str1.len() - k);
        }
        
        assert(forall|i1_check: int, j1_check: int| 
            0 <= i1_check <= str1.len() - k && 
            j1_check == i1_check + k ==> 
            is_not_substring_pred(str1.subrange(i1_check, j1_check), str2)) by {
            assert(forall|idx: int| 0 <= idx <= str1.len() - k ==> is_not_substring_pred(str1.subrange(idx, idx + k as int), str2));
        }
        
        assert(have_not_common_k_substring_pred(k, str1, str2));
        lemma_have_not_common_k_substring_equiv(k, str1, str2);
        assert(!have_common_k_substring_pred(k, str1, str2));
    }
    false
}
// </vc-code>

fn main() {}

}