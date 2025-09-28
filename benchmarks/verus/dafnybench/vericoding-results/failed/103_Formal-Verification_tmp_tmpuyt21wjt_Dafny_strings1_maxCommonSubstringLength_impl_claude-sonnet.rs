use vstd::prelude::*;

verus! {

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    assume(false);
    true
}

spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}

spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && (exists|i: int| 0 <= i <= str.len() && is_prefix_predicate(sub, str.subrange(i, str.len() as int)))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str),
{
    assume(false);
    true
}

spec fn have_common_k_substring_predicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && (exists|i: int| 0 <= i <= str1.len() - k && is_substring_predicate((str1.subrange(i, str1.len() as int)).subrange(0, k as int), str2))
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k <= usize::MAX,
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k as nat, str1, str2) == found,
{
    assume(false);
    true
}

spec fn max_common_substring_predicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool {
    forall|k: int| len < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2)
}

// <vc-helpers>
proof fn lemma_max_common_substring_bounded(str1: Seq<char>, str2: Seq<char>)
    ensures forall|k: nat| k > str1.len() || k > str2.len() ==> !have_common_k_substring_predicate(k, str1, str2)
{
    assert(forall|k: nat| k > str1.len() ==> !have_common_k_substring_predicate(k, str1, str2)) by {
        assert(forall|k: nat| k > str1.len() ==> str1.len() < k);
    };
    assert(forall|k: nat| k > str2.len() ==> !have_common_k_substring_predicate(k, str1, str2)) by {
        assert(forall|k: nat| k > str2.len() ==> str2.len() < k);
    };
}

proof fn lemma_max_exists(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    ensures 
        len <= str1.len() && len <= str2.len(),
        max_common_substring_predicate(str1, str2, len),
{
    let min_len = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
    lemma_max_common_substring_bounded(str1, str2);
    
    proof {
        let mut candidate: int = min_len as int;
        while candidate > 0
            invariant 
                candidate <= min_len,
                forall|k: int| candidate < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2),
            decreases candidate,
        {
            if !have_common_k_substring(candidate as usize, str1, str2) {
                candidate = candidate - 1;
            } else {
                break;
            }
        }
    }
    
    0nat
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    ensures 
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        max_common_substring_predicate(str1, str2, len as nat),
// </vc-spec>
// <vc-code>
{
    if str1.len() == 0 || str2.len() == 0 {
        return 0;
    }
    
    let min_len = if str1.len() <= str2.len() { str1.len() } else { str2.len() };
    
    let mut candidate: nat = min_len as nat;
    while candidate > 0
        invariant 
            candidate <= min_len,
            forall|k: int| candidate < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2),
        decreases candidate,
    {
        if have_common_k_substring(candidate as usize, str1, str2) {
            break;
        }
        candidate = candidate - 1;
    }
    
    proof {
        lemma_max_common_substring_bounded(str1, str2);
        assert(candidate <= str1.len() && candidate <= str2.len());
        assert(forall|k: int| candidate < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2));
    }
    
    candidate as usize
}
// </vc-code>

fn main() {}

}