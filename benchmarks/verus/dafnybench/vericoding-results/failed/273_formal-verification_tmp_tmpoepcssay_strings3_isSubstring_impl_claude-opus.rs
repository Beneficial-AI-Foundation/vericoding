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
    true
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
proof fn lemma_is_substring_iff_not_is_not_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) <==> !is_not_substring_pred(sub, str),
        is_not_substring_pred(sub, str) <==> !is_substring_pred(sub, str),
{
    if is_substring_pred(sub, str) {
        // There exists an i where sub is a prefix
        let i = choose|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int));
        assert(0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int)));
        assert(!is_not_substring_pred(sub, str));
    } else {
        // For all i, sub is not a prefix
        assert forall|i: int| 0 <= i <= str.len() implies is_not_prefix_pred(sub, str.subrange(i, str.len() as int)) by {
            if 0 <= i <= str.len() {
                if is_prefix_pred(sub, str.subrange(i, str.len() as int)) {
                    assert(is_substring_pred(sub, str));
                    assert(false);
                }
            }
        }
        assert(is_not_substring_pred(sub, str));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        res ==> is_substring_pred(sub, str),
        // ensures  !res ==> !is_substring_pred(sub, str)
        is_substring_pred(sub, str) ==> res,
        is_substring_pred(sub, str) ==> res,
        !res <==> is_not_substring_pred(sub, str), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i <= str.len() as usize
        invariant
            0 <= i <= str.len() as usize + 1,
            forall|j: int| 0 <= j < i as int ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
    {
        if i == str.len() as usize + 1 {
            break;
        }
        
        if i > str.len() as usize {
            i = i + 1;
            continue;
        }
        
        let suffix = str.subrange(i as int, str.len() as int);
        let is_pref = is_prefix(sub, suffix);
        
        if is_pref {
            proof {
                assert(is_prefix_pred(sub, str.subrange(i as int, str.len() as int)));
                assert(is_substring_pred(sub, str));
                lemma_is_substring_iff_not_is_not_substring(sub, str);
            }
            return true;
        }
        
        proof {
            assert(is_not_prefix_pred(sub, str.subrange(i as int, str.len() as int)));
        }
        i = i + 1;
    }
    
    proof {
        assert forall|j: int| 0 <= j <= str.len() implies is_not_prefix_pred(sub, str.subrange(j, str.len() as int)) by {
            if 0 <= j <= str.len() {
                if j < i as int {
                    assert(is_not_prefix_pred(sub, str.subrange(j, str.len() as int)));
                } else {
                    assert(j >= i as int);
                    assert(i <= str.len() as usize + 1);
                    if i == str.len() as usize + 1 {
                        assert(j <= str.len());
                        assert(j >= str.len() as int + 1);
                        assert(false);
                    } else {
                        assert(i <= str.len() as usize);
                        assert(j >= i as int);
                        assert(j <= str.len());
                        assert(false);
                    }
                }
            }
        }
        
        assert(is_not_substring_pred(sub, str));
        lemma_is_substring_iff_not_is_not_substring(sub, str);
        assert(!is_substring_pred(sub, str));
    }
    false
}
// </vc-code>

fn main() {}

}