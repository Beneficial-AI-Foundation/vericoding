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
#[verifier::decreases(sub.len(), 0usnat)]
spec fn is_prefix_spec(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    forall |k: int| 0 <= k < pre.len() ==> #[trigger] pre[k] == str[k]
}

spec fn is_substring_spec(sub: Seq<char>, str: Seq<char>) -> bool {
    sub.len() <= str.len() && 
    exists |i: int| 0 <= i <= str.len() - sub.len() && 
    forall |k: int| 0 <= k <= sub.len() ==> #[trigger] sub[k] == str[i + k]
}

proof fn lemma_prefix_pred_equiv(pre: Seq<char>, str: Seq<char>) 
    requires pre.len() <= str.len()
    ensures is_prefix_pred(pre, str) <==> is_prefix_spec(pre, str)
{
    // Since sequences are equal if lengths match and all elements match
    assert(pre == str.subrange(0, pre.len() as int))
        <==> pre.len() == str.subrange(0, pre.len() as int).len() && (forall |k| 0 <= k < pre.len() ==> pre[k] == str.subrange(0, pre.len() as int)[k]);
    assert(str.subrange(0, pre.len() as int)[k] == str[k]);
}

proof fn lemma_substring_pred_equiv(sub: Seq<char>, str: Seq<char>)
    requires sub.len() <= str.len()
    ensures is_substring_pred(sub, str) <==> is_substring_spec(sub, str)
{
    // Follows from lemma_prefix_pred_equiv applied to subranges
    if is_substring_pred(sub, str) {
        assert(exists |i| 0 <= i <= str.len() as nat && is_prefix_pred(sub, str.subrange(i as int, str.len() as int - i as int)));
        let i = choose |ix| 0 <= ix <= str.len() as nat - sub.len() as nat && is_prefix_pred(sub, str.subrange(ix as int, str.len() as int - ix as int));
        lemma_prefix_pred_equiv(sub, str.subrange(i as int, str.len() as int - i as int));
        assert(is_prefix_spec(sub, str.subrange(i as int, str.len() as int - i as int)));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> is_substring_pred(sub, str)
    //ensures !res <==> is_not_substring_pred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let sub_len = sub.len();
    let str_len = str.len();

    if sub_len > str_len {
        return false;
    }

    let mut i: usize = 0;
    while i <= str_len - sub_len
        invariant
            forall |k: int| 0 <= k < i as int ==> !(forall |m: int| 0 <= m < sub_len as int ==> sub[m] == str[k + m]),
            i <= str_len - sub_len + 1,
            sub_len <= str_len,
    {
        let mut is_match = true;
        let mut j: usize = 0;
        while j < sub_len
            invariant
                j <= sub_len,
                is_match ==> forall |m: int| 0 <= m < j as int ==> sub[m] == str[i as int + m],
                !is_match ==> exists |m: int| 0 <= m < sub_len as int && sub[m] != str[i as int + m],
        {
            if sub[j] != str[i + j] {
                is_match = false;
                break;
            }
            j = j + 1;
        }
        if is_match {
            proof { lemma_substring_pred_equiv(sub, str); };
            assert(is_substring_spec(sub, str));
            assert(is_substring_pred(sub, str));
            return true;
        }
        i = i + 1;
    }
    assert(forall |k: int| 0 <= k <= str_len as int - sub_len as int ==> !(forall |m: int| 0 <= m < sub_len as int ==> sub[m] == str[k + m]));
    assert(!is_substring_spec(sub, str));
    proof { lemma_substring_pred_equiv(sub, str); };
    assert(!is_substring_pred(sub, str));
    return false;
}
// </vc-code>

fn main() {}

}