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
proof lemma is_prefix_neg_lemma(pre: Seq<char>, str: Seq<char>)
    ensures
        is_prefix_pred(pre, str) <==> !is_not_prefix_pred(pre, str)
{
    reveal(is_prefix_pred);
    reveal(is_not_prefix_pred);
    assert(is_prefix_pred(pre, str) == !is_not_prefix_pred(pre, str));
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
    let n = str.len() as int;
    let m = sub.len() as int;

    if m == 0 {
        return true;
    }
    if m > n {
        return false;
    }

    for i in 0..=(n-m)
        invariant 
            forall|j: int| 0<=j<i ==> #[trigger] is_not_prefix_pred(sub, str.subrange(j, n))
    {
        if sub == str.subrange(i, i+m) {
            return true;
        } else {
            proof {
                let s = str.subrange(i, n);
                assert(s.subrange(0, m) == str.subrange(i, i+m));
                assert(sub != s.subrange(0, m));
                assert(is_not_prefix_pred(sub, s));
            }
        }
    }

    proof {
        assert forall|j: int| (n-m+1 <= j <= n) implies #[trigger] is_not_prefix_pred(sub, str.subrange(j, n))
        by {
            let s = str.subrange(j, n);
            assert(s.len() == n - j);
            assert(n - j < m);
            assert(sub.len() > s.len());
            assert(is_not_prefix_pred(sub, s));
        }
    }

    return false;
}
// </vc-code>

fn main() {}

}