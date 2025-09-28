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
proof fn is_prefix_pred_implies_len(pre: Seq<char>, str: Seq<char>)
    requires
        is_prefix_pred(pre, str),
    ensures
        pre.len() <= str.len()
{
}

proof fn is_not_prefix_pred_implies_len_or_diff(pre: Seq<char>, str: Seq<char>)
    requires
        is_not_prefix_pred(pre, str),
    ensures
        pre.len() > str.len() || pre != str.subrange(0, pre.len() as int)
{
}

proof fn is_substring_pred_implies_exists_index(sub: Seq<char>, str: Seq<char>)
    requires
        is_substring_pred(sub, str),
    ensures
        exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
{
}

proof fn is_not_substring_pred_implies_forall_index(sub: Seq<char>, str: Seq<char>)
    requires
        is_not_substring_pred(sub, str),
    ensures
        forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
{
}

proof fn have_common_k_substring_pred_implies_exists(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        have_common_k_substring_pred(k, str1, str2),
    ensures
        exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
{
}

proof fn have_not_common_k_substring_pred_implies_forall(k: nat, str1: Seq<char>, str2: Seq<char>)
    requires
        have_not_common_k_substring_pred(k, str1, str2),
    ensures
        forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
{
}
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
        false
    } else {
        let mut i: nat = 0;
        while i < pre.len()
            invariant
                0 <= i <= pre.len(),
                forall|j: nat| j < i ==> pre@[j] == str@[j],
        {
            proof {
                assert(i < pre.len());
                assert(i < str.len()); // Since pre.len() <= str.len()
            }
            if pre[i] != str[i] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

fn main() {
}

}