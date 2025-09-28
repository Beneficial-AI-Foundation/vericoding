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
spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len())
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    if pre.len() > str.len() {
        false
    } else {
        pre == str.subrange(0, pre.len())
    }
}

spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && pre == str.subrange(0, pre.len())
}

spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && (exists|i: usize| i <= str.len() - sub.len() && is_prefix_predicate(sub, str.subrange(i, str.len())))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str),
{
    if sub.len() > str.len() {
        false
    } else {
        let mut i: usize = 0;
        let len_sub: usize = sub.len();
        let len_str: usize = str.len();
        assert(len_sub <= len_str);
        while i <= len_str - len_sub
            invariant
                0 <= i <= len_str - len_sub + 1,
                forall|j: usize| j < i ==> !#[trigger] is_prefix_predicate(sub, str.subrange(j, len_str)),
        {
            let rest = str.subrange(i, len_str);
            if is_prefix(sub, rest) {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

spec fn have_common_k_substring_predicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && (exists|i: usize| i <= str1.len() - k && is_substring_predicate((str1.subrange(i, str1.len())).subrange(0, k), str2))
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k <= usize::MAX,
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k as nat, str1, str2) == found,
{
    if k > str1.len() || k > str2.len() {
        false
    } else {
        let mut i: usize = 0;
        let len1: usize = str1.len();
        let len2: usize = str2.len();
        while i <= len1 - k
            invariant
                0 <= i <= len1 - k + 1,
                forall|j: usize| j < i ==> !#[trigger] is_substring_predicate(str1.subrange(j, j + k), str2),
        {
            let substr = str1.subrange(i, i + k);
            if is_substring(substr, str2) {
                return true;
            }
            i = i + 1;
        }
        false
    }
}

spec fn max_common_substring_predicate(str1: Seq<char>, str2: Seq<char>, len: nat) -> bool {
    forall|k: int| len < k <= str1.len() ==> !#[trigger] have_common_k_substring_predicate(k as nat, str1, str2)
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
    let min_len: usize = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    let mut k: usize = min_len;
    let mut found: bool = false;
    let mut len: usize = 0;
    while k >= 1
        invariant
            k >= 0,
            k <= min_len + 1,
            !found ==> forall|p: int| p > k && p <= min_len ==> !#[trigger] have_common_k_substring_predicate(p as nat, str1, str2),
            found ==> have_common_k_substring_predicate(len as nat, str1, str2) && forall|p: int| p > len as int && p <= min_len ==> !#[trigger] have_common_k_substring_predicate(p as nat, str1, str2)
    {
        if have_common_k_substring(k, str1, str2) {
            found = true;
            len = k;
            proof {
                assert(have_common_k_substring_predicate(k as nat, str1, str2));
                assert(forall|p: int| p > min_len ==> !#[trigger] have_common_k_substring_predicate(p as nat, str1, str2));
            }
        }
        if k == 0 {
            break;
        }
        k = k - 1;
    }
    if !found {
        proof {
            assert(forall|p: int| p > 0 && p as nat <= str1.len() as nat && p as nat <= str2.len() as nat ==> !#[trigger] have_common_k_substring_predicate(p as nat, str1, str2));
        }
    }
    len
}
// </vc-code>

fn main() {}

}