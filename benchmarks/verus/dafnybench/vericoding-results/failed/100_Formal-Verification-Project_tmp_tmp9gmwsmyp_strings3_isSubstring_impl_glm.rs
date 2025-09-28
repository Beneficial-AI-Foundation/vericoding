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
fn check_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> is_prefix_pred(pre, str),
{
    let pre_len = pre.len();
    let str_len = str.len();
    if pre_len > str_len {
        return false;
    }
    let mut i = 0;
    while i < pre_len
        invariant 0 <= i <= pre_len
        invariant forall|j: int| 0 <= j < i ==> pre@[j] == str@[j]
    {
        if pre@[i] != str@[i] {
            return false;
        }
        i = i + 1;
    }
    true
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
        assert(is_substring_pred(sub, str));
        true
    } else {
        let mut i = 0;
        let n = str.len();
        let m = sub.len();
        while i <= n - m
            invariant 0 <= i <= n - m + 1
            invariant forall|j: int| 0 <= j < i ==> !is_prefix_pred(sub, str.subrange(j, n as int))
        {
            if check_prefix(sub, str.subrange(i, n as int)) {
                proof {
                    assert(is_prefix_pred(sub, str.subrange(i, n as int)));
                    assert(is_substring_pred(sub, str));
                }
                return true;
            }
            proof {
                assert(is_prefix_pred(sub, str.subrange(i, n as int)) == false);
                is_prefix_iff_not_not(sub, str.subrange(i, n as int));
                assert(is_not_prefix_pred(sub, str.subrange(i, n as int)));
            }
            i = i + 1;
        }
        proof {
            assert(forall|j: int| 0 <= j <= n - m ==> is_not_prefix_pred(sub, str.subrange(j, n as int)));
            assert(forall|j: int| 0 <= j <= n ==> {
                if j <= n - m {
                    is_not_prefix_pred(sub, str.subrange(j, n as int))
                } else {
                    let sub_len = sub.len();
                    let sub_str_len = str.subrange(j, n as int).len();
                    assert(sub_len == m);
                    assert(sub_str_len == n - j);
                    assert(n - j < m);
                    assert(is_not_prefix_pred(sub, str.subrange(j, n as int)));
                }
            });
            assert(is_not_substring_pred(sub, str));
            is_substring_lemma(sub, str);
        }
        false
    }
}
// </vc-code>

fn main() {}

}