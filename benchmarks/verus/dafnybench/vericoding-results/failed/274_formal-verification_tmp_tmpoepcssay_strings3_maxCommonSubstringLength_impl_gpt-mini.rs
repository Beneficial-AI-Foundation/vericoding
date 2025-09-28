use vstd::prelude::*;

verus! {

spec fn is_substring(sub: Seq<char>, str: Seq<char>) -> bool 
    decreases str.len()
{
    if sub.len() == 0 {
        true
    } else if str.len() < sub.len() {
        false
    } else {
        (str.subrange(0, sub.len() as int) == sub) || is_substring(sub, str.subrange(1, str.len() as int))
    }
}

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| #![auto] 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| #![auto] 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    assume(false);
    false
}

// <vc-helpers>
fn common_k_exists(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    let n1 = str1.len();
    let n2 = str2.len();

    if k > n1 {
        return (false);
    }

    let n1i: int = n1 as int;
    let n2i: int = n2 as int;
    let ki: int = k as int;

    // iterate over all possible substrings of str1 of length k
    let mut i1: int = 0;
    while i1 <= n1i - ki
        invariant 0 <= i1 && i1 <= n1i - ki + 1
        invariant forall|x: int| #[trigger] ((0 <= x && x < i1) ==> is_not_substring_pred(str1.subrange(x, x + ki), str2))
    {
        let j1i: int = i1 + ki;
        let sub = str1.subrange(i1, j1i);

        // search sub in str2
        let max_i2i: int = if n2i >= ki { n2i - ki } else { 0 };
        let mut i2: int = 0;
        while i2 <= max_i2i
            invariant 0 <= i2 && i2 <= max_i2i + 1
            invariant forall|y: int| #[trigger] ((0 <= y && y < i2) ==> str2.subrange(y, y + ki) != sub)
        {
            if n2 >= k && str2.subrange(i2, i2 + ki) == sub {
                // Found matching substring of length k at positions i1 in str1 and i2 in str2.
                // This witnesses have_common_k_substring_pred.
                return (true);
            }
            i2 = i2 + 1;
        }

        // At this point, for this particular sub, no prefix of any suffix of str2 matches sub
        // for indices 0..=n2-k. Hence sub is not a substring of str2.
        proof {
            let sublen: int = ki;
            // From the inner loop invariant at termination (i2 = max_i2i + 1),
            // we have for all i in 0..=max_i2i: str2.subrange(i, i+sublen) != sub.
            if n2 >= k {
                // Then max_i2i = n2i - sublen
                assert(forall|i: int| #[trigger] ((0 <= i && i <= n2i - sublen) ==> str2.subrange(i, i + sublen) != sub));
            } else {
                // n2 < k, there are no indices with suffix length >= sublen,
                // so the universal claim over an empty range vacuously holds.
                assert(forall|i: int| #[trigger] ((0 <= i && i <= n2i - sublen) ==> str2.subrange(i, i + sublen) != sub));
            }

            // Now show: forall i in 0..=n2, is_not_prefix_pred(sub, str2.subrange(i,n2))
            assert(forall|i: int| #[trigger] ((0 <= i && i <= n2i) ==>
                {
                    if i <= n2i - sublen {
                        // Then the suffix starting at i has length >= sublen, and its prefix of length sublen
                        // equals str2.subrange(i, i+sublen), which we know is not equal to sub.
                        let suffix = str2.subrange(i, n2i);
                        !is_prefix_pred(sub, suffix)
                    } else {
                        // Remaining suffix is shorter than sub, so pre.len() > suffix.len()
                        // hence is_not_prefix_pred holds.
                        true
                    }
                }));

            // From above, for all i we have is_not_prefix_pred(sub, str2.subrange(i,n2)), i.e., is_not_substring_pred
            assert(is_not_substring_pred(sub, str2));
        }

        i1 = i1 + 1;
    }

    // No substring of length k in str1 is a substring of str2
    proof {
        // From outer loop invariant when i1 = n1i - ki + 1, we have for all i1' in 0..=n1-k : is_not_substring_pred(...)
        assert(forall|x: int| #[trigger] ((0 <= x && x <= n1i - ki) ==> is_not_substring_pred(str1.subrange(x, x + ki), str2)));
        // This is exactly have_not_common_k_substring_pred
        assert(have_not_common_k_substring_pred(k as nat, str1, str2));
    }

    (false)
}
// </vc-helpers>

// <vc-spec>
fn max_common_substring_length(str1: Seq<char>, str2: Seq<char>) -> (len: usize)
    requires str1.len() <= str2.len(),
    ensures 
        forall|k: nat| #![auto] len < k <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
        have_common_k_substring_pred(len as nat, str1, str2),
// </vc-spec>
// <vc-code>
{
    let n1: usize = str1.len();
    let n2: usize = str2.len();
    // Precondition ensures n1 <= n2
    let mut k: usize = n1;
    // We will search from largest possible length downwards, maintaining that
    // all lengths greater than current k and <= n1 have no common substring.
    while k > 0
        invariant k <= n1 + 1
        invariant forall|kk: int| #[trigger] ((0 <= kk && kk <= n1 as int && kk > k as int) ==> have_not_common_k_substring_pred(kk as nat, str1, str2))
    {
        let exists_common = common_k_exists(k, str1, str2);
        if exists_common {
            return k;
        }
        k = k - 1;
    }
    // k == 0
    0
}
// </vc-code>

fn main() {
}

}