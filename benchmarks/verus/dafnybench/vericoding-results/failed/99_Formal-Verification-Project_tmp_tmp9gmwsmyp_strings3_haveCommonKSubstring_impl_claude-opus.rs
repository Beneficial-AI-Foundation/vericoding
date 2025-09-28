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
proof fn lemma_is_not_substring_iff_not_is_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_not_substring_pred(sub, str) <==> !is_substring_pred(sub, str),
{
    // The equivalence follows from the definitions of is_substring_pred and is_not_substring_pred
    // is_substring_pred: exists i such that prefix holds
    // is_not_substring_pred: forall i, prefix doesn't hold
    // These are logical negations of each other
}

proof fn lemma_have_not_common_k_substring_iff_not_have_common(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_not_common_k_substring_pred(k, str1, str2) <==> !have_common_k_substring_pred(k, str1, str2),
{
    if have_not_common_k_substring_pred(k, str1, str2) {
        assert forall|i1: int, j1: int| 
            0 <= i1 <= str1.len() - k && j1 == i1 + k implies
            is_not_substring_pred(str1.subrange(i1, j1), str2) by {}
        
        assert forall|i1: int, j1: int| 
            0 <= i1 <= str1.len() - k && j1 == i1 + k implies
            !is_substring_pred(str1.subrange(i1, j1), str2) by {
            if 0 <= i1 <= str1.len() - k && j1 == i1 + k {
                lemma_is_not_substring_iff_not_is_substring(str1.subrange(i1, j1), str2);
            }
        }
        
        assert(!have_common_k_substring_pred(k, str1, str2));
    } else {
        assert(!have_not_common_k_substring_pred(k, str1, str2));
        // Need to show have_common_k_substring_pred(k, str1, str2)
        // Since not forall i1,j1: P, there exists i1,j1: !P
        assert(exists|i1: int, j1: int| 
            0 <= i1 <= str1.len() - k && j1 == i1 + k && 
            !is_not_substring_pred(str1.subrange(i1, j1), str2));
        
        assert(exists|i1: int, j1: int| 
            0 <= i1 <= str1.len() - k && j1 == i1 + k && 
            is_substring_pred(str1.subrange(i1, j1), str2)) by {
            let i1 = choose|i1: int, j1: int| 
                0 <= i1 <= str1.len() - k && j1 == i1 + k && 
                !is_not_substring_pred(str1.subrange(i1, j1), str2);
            let j1 = i1 + k;
            lemma_is_not_substring_iff_not_is_substring(str1.subrange(i1, j1), str2);
            assert(is_substring_pred(str1.subrange(i1, j1), str2));
        }
        
        assert(have_common_k_substring_pred(k, str1, str2));
    }
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
        assert(have_common_k_substring_pred(k, str1, str2)) by {
            assert(0 <= 0 <= str1.len() - k);
            assert(0 + k == 0);
            assert(str1.subrange(0, 0).len() == 0);
            assert(is_substring_pred(str1.subrange(0, 0), str2));
        }
        return true;
    }
    
    if str1.len() < k {
        assert(have_not_common_k_substring_pred(k, str1, str2)) by {
            assert forall|i1: int, j1: int| 
                0 <= i1 <= str1.len() - k && j1 == i1 + k implies
                is_not_substring_pred(str1.subrange(i1, j1), str2) by {
                assert(str1.len() - k < 0);
                assert(!(0 <= i1 <= str1.len() - k));
            }
        }
        lemma_have_not_common_k_substring_iff_not_have_common(k, str1, str2);
        return false;
    }
    
    let mut i1: usize = 0;
    while i1 <= str1.len() - k
        invariant
            i1 <= str1.len() - k + 1,
            forall|ii: int| 0 <= ii < i1 ==> !is_substring_pred(str1.subrange(ii, ii + k), str2),
    {
        let j1 = i1 + k;
        let sub = str1.subrange(i1 as int, j1 as int);
        
        if is_substring(sub, str2) {
            assert(have_common_k_substring_pred(k, str1, str2)) by {
                assert(0 <= i1 <= str1.len() - k);
                assert(j1 == i1 + k);
                assert(is_substring_pred(str1.subrange(i1 as int, j1 as int), str2));
            }
            return true;
        }
        
        i1 = i1 + 1;
    }
    
    assert(have_not_common_k_substring_pred(k, str1, str2)) by {
        assert forall|ii: int, jj: int| 
            0 <= ii <= str1.len() - k && jj == ii + k implies
            is_not_substring_pred(str1.subrange(ii, jj), str2) by {
            if 0 <= ii <= str1.len() - k && jj == ii + k {
                assert(!is_substring_pred(str1.subrange(ii, jj), str2));
                lemma_is_not_substring_iff_not_is_substring(str1.subrange(ii, jj), str2);
            }
        }
    }
    lemma_have_not_common_k_substring_iff_not_have_common(k, str1, str2);
    false
}
// </vc-code>

fn main() {}

}