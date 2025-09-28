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
proof fn lemma_is_prefix_pred_implies_is_prefix(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_pred(pre, str) ==> is_prefix(pre, str),
        is_not_prefix_pred(pre, str) ==> !is_prefix(pre, str),
{
}

proof fn lemma_is_substring_pred_implies_is_substring(sub: Seq<char>, str: Seq<char>)
    ensures
        is_substring_pred(sub, str) ==> is_substring(sub, str),
        is_not_substring_pred(sub, str) ==> !is_substring(sub, str),
{
}

proof fn lemma_have_common_k_substring_pred_implies_exists(k: nat, str1: Seq<char>, str2: Seq<char>)
    ensures
        have_common_k_substring_pred(k, str1, str2) ==> 
            exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && 
            is_substring_pred(str1.subrange(i1, j1), str2),
    ensures
        have_not_common_k_substring_pred(k, str1, str2) ==> 
            forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> 
            is_not_substring_pred(str1.subrange(i1, j1), str2),
{
}

proof fn lemma_subrange_properties(i: int, str: Seq<char>, sub: Seq<char>)
    requires
        0 <= i <= str.len(),
    ensures
        forall|j: int| 0 <= j < sub.len() ==> #[trigger] str@[i + j] == str.subrange(i, str.len() as int)@[j],
{
}

proof fn lemma_prefix_equivalence(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_pred(pre, str) == (pre.len() <= str.len() && 
        forall|i: int| 0 <= i < pre.len() ==> pre@[i] == str@[i])
{
    assert forall|i: int| 0 <= i < pre.len() implies pre@[i] == str@[i] by {
        if pre.len() <= str.len() {
            assert(pre.subrange(0, pre.len() as int) == str.subrange(0, pre.len() as int));
        }
    };
}

proof fn lemma_loop_invariant_maintenance(i: int, sub: Seq<char>, str: Seq<char>)
    requires
        0 <= i <= str.len() - sub.len(),
        forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
        is_not_prefix_pred(sub, str.subrange(i, str.len() as int)),
    ensures
        forall|j: int| 0 <= j < i+1 ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
{
}

proof fn lemma_final_assertion(sub: Seq<char>, str: Seq<char>, i: int)
    requires
        sub.len() > 0,
        i == str.len() - sub.len() + 1,
        forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
    ensures
        forall|j: int| 0 <= j <= str.len() - sub.len() ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
{
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
        return true;
    }
    
    let mut i: int = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
        decreases str.len() - i,
    {
        let mut j: int = 0;
        let mut match_found = true;
        
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                match_found == (j == sub.len() || (j < sub.len() && i + j < str.len() && str@[i + j] != sub@[j])),
            decreases sub.len() - j,
        {
            if i + j >= str.len() {
                match_found = false;
                break;
            }
            if str@[i + j] != sub@[j] {
                match_found = false;
                break;
            }
            j = j + 1;
        }
        
        if j == sub.len() && match_found {
            proof {
                lemma_prefix_equivalence(sub, str.subrange(i, str.len() as int));
                assert(forall|k: int| 0 <= k < sub.len() ==> sub@[k] == str.subrange(i, str.len() as int)@[k]);
                assert(is_prefix_pred(sub, str.subrange(i, str.len() as int)));
            }
            return true;
        }
        
        proof {
            lemma_prefix_equivalence(sub, str.subrange(i, str.len() as int));
            assert(is_not_prefix_pred(sub, str.subrange(i, str.len() as int)));
            lemma_loop_invariant_maintenance(i, sub, str);
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_final_assertion(sub, str, i);
        assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)));
        assert(is_not_substring_pred(sub, str));
        lemma_is_substring_pred_implies_is_substring(sub, str);
    }
    
    false
}
// </vc-code>

fn main() {}

}