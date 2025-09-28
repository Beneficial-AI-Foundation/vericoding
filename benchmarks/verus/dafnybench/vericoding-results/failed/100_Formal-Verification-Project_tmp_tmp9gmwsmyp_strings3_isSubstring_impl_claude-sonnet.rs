use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_is_not_substring_equiv(sub: Seq<char>, str: Seq<char>)
    ensures is_not_substring_pred(sub, str) <==> !is_substring_pred(sub, str)
{
    if is_substring_pred(sub, str) {
        let i = choose|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int));
        assert(!is_not_prefix_pred(sub, str.subrange(i, str.len() as int)));
        assert(!is_not_substring_pred(sub, str));
    }
    
    if !is_substring_pred(sub, str) {
        assert(forall|i: int| 0 <= i <= str.len() ==> !is_prefix_pred(sub, str.subrange(i, str.len() as int)));
        assert(forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int)));
        assert(is_not_substring_pred(sub, str));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> is_substring_pred(sub, str)
    //ensures !res <==> is_not_substring_pred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if sub.len() == 0 {
        assert(is_prefix_pred(sub, str.subrange(0, str.len() as int))) by {
            assert(sub.len() <= str.len());
            assert(sub == str.subrange(0, sub.len() as int)) by {
                assert(sub.len() == 0);
                assert(str.subrange(0, 0).len() == 0);
            }
        }
        assert(is_substring_pred(sub, str));
        return true;
    }
    
    let mut i: usize = 0;
    while i <= str.len()
        invariant 
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int))
    {
        if i == str.len() + 1 {
            break;
        }
        
        proof {
            let i_int = i as int;
            let str_len_int = str.len() as int;
            let suffix = str.subrange(i_int, str_len_int);
            let is_prefix_here = is_prefix(sub, suffix);
            
            if is_prefix_here {
                assert(is_prefix_pred(sub, suffix));
                assert(is_substring_pred(sub, str));
                return true;
            } else {
                assert(is_not_prefix_pred(sub, suffix));
            }
        }
        
        let i_int = i as ghost int;
        let str_len_int = str.len() as ghost int;
        let suffix = str.subrange(i_int, str_len_int);
        let is_prefix_here = is_prefix(sub, suffix);
        
        if is_prefix_here {
            return true;
        }
        
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j <= str.len() ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)));
    assert(is_not_substring_pred(sub, str));
    proof {
        lemma_is_not_substring_equiv(sub, str);
    }
    assert(!is_substring_pred(sub, str));
    false
}
// </vc-code>

fn main() {}

}