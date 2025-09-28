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
proof fn lemma_not_prefix_equiv(pre: Seq<char>, str: Seq<char>)
    ensures
        is_not_prefix_pred(pre, str) <==> !is_prefix_pred(pre, str)
{
    assert(
        is_not_prefix_pred(pre, str)
        == (pre.len() > str.len() || pre != str.subrange(0, pre.len() as int))
    );
    assert(
        is_prefix_pred(pre, str)
        == (pre.len() <= str.len() && pre == str.subrange(0, pre.len() as int))
    );
    assert(
        (pre.len() > str.len() || pre != str.subrange(0, pre.len() as int))
        <==> !(pre.len() <= str.len() && pre == str.subrange(0, pre.len() as int))
    );
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
    proof {
        lemma_not_prefix_equiv(pre, str);
    }
    let res = is_prefix_pred(pre, str);
    proof {
        assert(res <==> is_prefix_pred(pre, str));
        assert(is_not_prefix_pred(pre, str) <==> !is_prefix_pred(pre, str));
        assert(!res <==> is_not_prefix_pred(pre, str));
    }
    res
}
// </vc-code>

fn main() {
}

}