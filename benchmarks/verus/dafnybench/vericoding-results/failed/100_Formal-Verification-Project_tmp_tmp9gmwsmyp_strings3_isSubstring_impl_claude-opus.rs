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
proof fn lemma_not_substring_implies_forall_not_prefix(sub: Seq<char>, str: Seq<char>)
    ensures
        !is_substring_pred(sub, str) ==> is_not_substring_pred(sub, str),
{
    if !is_substring_pred(sub, str) {
        assert forall|i: int| 0 <= i <= str.len() implies is_not_prefix_pred(sub, str.subrange(i, str.len() as int)) by {
            if 0 <= i <= str.len() {
                if is_prefix_pred(sub, str.subrange(i, str.len() as int)) {
                    assert(is_substring_pred(sub, str));
                    assert(false);
                }
            }
        }
    }
}

proof fn lemma_forall_not_prefix_implies_not_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_not_substring_pred(sub, str) ==> !is_substring_pred(sub, str),
{
    if is_not_substring_pred(sub, str) {
        if is_substring_pred(sub, str) {
            let i = choose|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int));
            assert(is_not_prefix_pred(sub, str.subrange(i, str.len() as int)));
            assert(false);
        }
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
    let mut i: usize = 0;
    while i <= str.len() as usize
        invariant
            0 <= i <= str.len() + 1,
            forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
    {
        if i > str.len() as usize {
            proof {
                lemma_not_substring_implies_forall_not_prefix(sub, str);
            }
            return false;
        }
        
        let suffix = str.subrange(i as int, str.len() as int);
        if is_prefix(sub, suffix) {
            proof {
                assert(is_substring_pred(sub, str));
            }
            return true;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_not_substring_implies_forall_not_prefix(sub, str);
    }
    false
}
// </vc-code>

fn main() {}

}