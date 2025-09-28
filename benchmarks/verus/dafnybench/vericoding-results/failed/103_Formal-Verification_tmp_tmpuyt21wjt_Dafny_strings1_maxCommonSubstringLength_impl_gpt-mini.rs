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
spec fn lcp_len(str1: Seq<char>, str2: Seq<char>, i: int, p: int) -> int {
    if i >= str1.len() || p >= str2.len() {
        0
    } else if str1@[i] == str2@[p] {
        1 + lcp_len(str1, str2, i + 1, p + 1)
    } else {
        0
    }
}

proof fn lcp_len_le_if_no_match(str1: Seq<char>, str2: Seq<char>, i: int, p: int, l: int)
    requires l >= 0,
    requires !(i + l < str1.len() && p + l < str2.len() && str1@[i + l] == str2@[p + l]),
    ensures lcp_len(str1, str2, i, p) <= l,
    decreases l,
{
    if l == 0 {
        if i >= str1.len() || p >= str2.len() {
            assert(lcp_len(str1, str2, i, p) == 0);
        } else {
            if str1@[i] == str2@[p] {
                assert(!(i + 0 < str1.len() && p + 0 < str2.len() && str1@[i + 0] == str2@[p + 0]));
            } else {
                assert(lcp_len(str1, str2, i, p) == 0);
            }
        }
    } else {
        if i >= str1.len() || p >= str2.len() {
            assert(lcp_len(str1, str2, i, p) == 0);
        } else {
            if str1@[i] == str2@[p] {
                lcp_len_le_if_no_match(str1, str2, i + 1, p + 1, l - 1);
                assert(lcp_len(str1, str2, i + 1, p + 1) <= l - 1);
                assert(lcp_len(str1, str2, i, p) == 1 + lcp_len(str1, str2, i + 1, p + 1));
                assert(lcp_len(str1, str2, i, p) <= l);
            } else {
                assert(lcp_len(str1, str2, i, p) == 0);
            }
        }
    }
}

proof fn lcp_len_ge_if_prefix(str1: Seq<char>, str2: Seq<char>, i: int, p: int, l: int)
    requires l >= 0,
    requires forall|j: int| 0 <= j && j < l ==> (i + j < str1.len() && p + j < str2.len() && str1@[i + j] == str2@[p + j]),
    ensures l <= lcp_len(str1, str2, i, p),
    decreases l,
{
    if l == 0 {
        // vacuously true
    } else {
        assert(i < str1.len() && p < str2.len() && str1@[i] == str2@[p]);
        lcp_len_ge_if_prefix(str1, str2, i + 1, p + 1, l - 1);
        assert(l - 1 <= lcp_len(str1, str2, i + 1, p + 1));
        assert(lcp_len(str1, str2, i, p) == 1 + lcp_len(str1, str2, i + 1, p + 1));
        assert(l <= lcp_len(str1, str2, i, p));
    }
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
    let n1: int = str1.len();
    let n2: int = str2.len();
    let mut best: int = 0;
    let mut i: int = 0;
    while i < n1
        invariant 0 <= i && i <= n1,
        invariant 0 <= best && best <= n1 && best <= n2,
        invariant forall|ii: int, pp: int| 0 <= ii && ii < i && 0 <= pp && pp < n2 ==> lcp_len(str1, str2, ii, pp) <= best,
    {
        let mut p: int = 0;
        while p < n2
            invariant 0 <= p && p <= n2,
            invariant 0 <= best && best <= n1 && best <= n2,
            invariant forall|ii: int, pp: int| 0 <= ii && ii < i && 0 <= pp && pp < n2 ==> lcp_len(str1, str2, ii, pp) <= best,
            invariant forall|pp: int| 0 <= pp && pp < p ==> lcp_len(str1, str2, i, pp) <= best,
        {
            let mut l: int = 0;
            while i + l < n1 && p + l < n2 && str1@[i + l] == str2@[p + l]
                invariant 0 <= l,
                invariant i + l <= n1 && p + l <= n2,
                invariant forall|j: int| 0 <= j && j < l ==> str1@[i + j] == str2@[p + j],
            {
                l = l + 1;
            }
            proof {
                lcp_len_ge_if_prefix(str1, str2, i, p, l);
            }
            assert(l <= lcp_len(str1, str2, i, p));
            proof {
                lcp_len_le_if_no_match(str1, str2, i, p, l);
            }
            assert(lcp_len(str1, str2, i, p) <= l);
            assert(l == lcp_len(str1, str2, i, p));
            if l > best {
                best = l;
            }
            assert(lcp_len(str1, str2, i, p) <= best);
            p = p + 1;
        }
        assert(forall|pp: int| 0 <= pp && pp < n2 ==> lcp_len(str1, str2, i, pp) <= best);
        i = i + 1;
    }
    assert(forall|ii: int, pp: int| 0 <= ii && ii < n1 && 0 <= pp && pp < n2 ==> lcp_len(str1, str2, ii, pp) <= best);
    assert(0 <= best);
    (best as usize)
}
// </vc-code>

fn main() {}

}