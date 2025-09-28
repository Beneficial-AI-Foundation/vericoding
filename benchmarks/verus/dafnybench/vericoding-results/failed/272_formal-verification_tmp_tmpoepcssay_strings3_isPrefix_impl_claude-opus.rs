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

// </vc-helpers>

// <vc-spec>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
// </vc-spec>
// <vc-code>
{
    if pre.len() > str.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] pre@[j] == str@[j],
    {
        if pre@[i] != str@[i] {
            proof {
                assert(pre@[i as int] != str@[i as int]);
                assert(pre@ != str@.subrange(0, pre.len() as int));
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i as int == pre.len());
        assert(forall|j: int| 0 <= j < pre.len() ==> #[trigger] pre@[j] == str@[j]);
        assert(pre@ =~= str@.subrange(0, pre.len() as int));
    }
    true
}
// </vc-code>

fn main() {
}

}