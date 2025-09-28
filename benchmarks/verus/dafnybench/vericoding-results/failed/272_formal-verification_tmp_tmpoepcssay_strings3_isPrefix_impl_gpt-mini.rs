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
// no helpers needed
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
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < pre.len()
        invariant 0 <= i && i <= pre.len();
        invariant ok ==> forall|k: int| 0 <= k && k < i ==> pre@[k] == str@[k];
        decreases pre.len() - i
    {
        if pre@[i] != str@[i] {
            ok = false;
            i = pre.len();
        } else {
            i = i + 1;
        }
    }
    if ok {
        // all indices < pre.len() match, so the prefix equals the corresponding subrange
        assert(forall|k: int| 0 <= k && k < pre.len() ==> pre@[k] == str.subrange(0, pre.len() as int)@[k]);
        assert(pre.len() == str.subrange(0, pre.len() as int).len());
        assert(pre == str.subrange(0, pre.len() as int));
    }
    ok
}
// </vc-code>

fn main() {
}

}