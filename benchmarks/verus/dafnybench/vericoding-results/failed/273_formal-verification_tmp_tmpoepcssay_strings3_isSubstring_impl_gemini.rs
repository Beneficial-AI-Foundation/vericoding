// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed redundant casts from previous attempt */
proof fn exec_is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_prefix_pred(pre, str),
        !res <==> is_not_prefix_pred(pre, str),
{
    if pre.len() > str.len() {
        assert(is_not_prefix_pred(pre, str));
        return false;
    }
    let mut i: int = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            pre.subrange(0, i) == str.subrange(0, i),
        decreases pre.len() - i
    {
        if pre[i] != str[i] {
            assert(pre.subrange(0, pre.len()) != str.subrange(0, pre.len()));
            assert(is_not_prefix_pred(pre, str));
            return false;
        }
        i = i + 1;
    }
    assert(pre.subrange(0, pre.len()) == str.subrange(0, pre.len()));
    assert(is_prefix_pred(pre, str));
    true
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_substring_pred(sub, str),
        res ==> is_substring_pred(sub, str),

        is_substring_pred(sub, str) ==> res,
        is_substring_pred(sub, str) ==> res,
        !res <==> is_not_substring_pred(sub, str),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mismatched types by using 'int' for the loop counter */
    let mut i: int = 0;
    while i <= str.len()
        invariant
            0 <= i <= str.len() + 1,
            forall|k: int| 0 <= k < i ==> is_not_prefix_pred(sub, str.subrange(k, str.len())),
        decreases str.len() - i
    {
        let ghost suffix = str.subrange(i, str.len());
        if exec_is_prefix(sub, suffix) {
            assert(is_prefix_pred(sub, str.subrange(i, str.len())));
            assert(is_substring_pred(sub, str));
            return true;
        }
        i = i + 1;
    }
    assert(is_not_substring_pred(sub, str));
    false
}
// </vc-code>

}
fn main() {}