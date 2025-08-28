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
spec fn seq_equal_up_to<T>(s1: Seq<T>, s2: Seq<T>, len: int) -> bool {
    forall|i: int| 0 <= i < len ==> s1@[i] == s2@[i]
}

proof fn prefix_implies_equal_up_to(pre: Seq<char>, str: Seq<char>)
    requires
        is_prefix_pred(pre, str),
    ensures
        seq_equal_up_to(pre, str, pre.len() as int),
{
    assert forall|i: int| 0 <= i < pre.len() implies pre@[i] == str@[i] by {
        assert(pre == str.subrange(0, pre.len() as int));
        assert(pre@[i] == str.subrange(0, pre.len() as int)@[i]);
        assert(str.subrange(0, pre.len() as int)@[i] == str@[i]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            i <= str.len(),
            forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
    {
        if pre@[i] != str@[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}