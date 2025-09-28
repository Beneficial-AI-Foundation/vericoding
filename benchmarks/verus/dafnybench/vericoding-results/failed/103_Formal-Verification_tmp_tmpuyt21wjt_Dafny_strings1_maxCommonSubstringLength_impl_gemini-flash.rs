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
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_predicate(pre, str),
{
    pre.len() <= str.len() && pre == str.subrange(0, pre.len() as int)
}

spec fn is_prefix_predicate(pre: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= pre.len() && pre == str.subrange(0, pre.len() as int)
}

spec fn is_substring_predicate(sub: Seq<char>, str: Seq<char>) -> bool {
    str.len() >= sub.len() && (exists|i: int| 0 <= i && i <= str.len() - sub.len() && is_prefix_predicate(sub, str.subrange(i, str.len() as int)))
}

fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res == is_substring_predicate(sub, str),
{
    let mut i: usize = 0;
    while (i + sub.len() <= str.len())
        invariant
            i as int <= str.len(),
            forall |j: int| 0 <= j < i ==> !is_prefix_predicate(sub, str.subrange(j, str.len() as int)),
    {
        if is_prefix(sub, str.subrange(i as int, str.len() as int)) {
            return true;
        }
        i = i + 1;
    }
    false
}

spec fn have_common_k_substring_predicate(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    str1.len() >= k && str2.len() >= k && (exists|i: int| 
        0 <= i && i <= str1.len() - k && 
        is_substring_predicate((str1.subrange(i, (i + k) as int)), str2)
    )
}

fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    requires k <= usize::MAX,
    ensures 
        (str1.len() < k || str2.len() < k) ==> !found,
        have_common_k_substring_predicate(k as nat, str1, str2) == found,
{
    if str1.len() < k || str2.len() < k {
        return false;
    }

    let mut i: usize = 0;
    while (i <= str1.len() - k)
        invariant
            i as int <= str1.len() - k + 1,
            forall |j: int| 0 <= j < i ==> !is_substring_predicate(str1.subrange(j, (j + k) as int), str2),
    {
        let sub = str1.subrange(i as int, (i + k) as int);
        if is_substring(sub, str2) {
            return true;
        }
        i = i + 1;
    }
    false
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
    let mut max_len: usize = 0;

    if str1.len() == 0 || str2.len() == 0 {
        return 0;
    }

    let min_possible_len = if str1.len() < str2.len() { str1.len() } else { str2.len() };

    // Iterate `k` from `min_possible_len` down to `1`.
    // If a common substring of length `k` is found, then this `k` is the maximum common substring length.
    // If no common substring is found for `k=1`, then the max common substring length is `0`.
    proof {
        assert forall|k: int| 0 <= k <= min_possible_len implies (
            have_common_k_substring_predicate(k as nat, str1, str2) == 
            (exists|i: int, j: int| 
                #[trigger] (0 <= i && i <= str1.len() - k && 
                0 <= j && j <= str2.len() - k && 
                str1.subrange(i, (i + k) as int) == str2.subrange(j, (j + k) as int)))
        ) by {
            assert forall|pre: Seq<char>, s: Seq<char>| s.len() >= pre.len() && pre == s.subrange(0, pre.len() as int) == is_prefix_predicate(pre, s) by {
                // This is a direct consequence of the definition
            }
            assert forall|sub: Seq<char>, s: Seq<char>| s.len() >= sub.len() && (exists|idx: int| 0 <= idx && idx <= s.len() - sub.len() && #[trigger] is_prefix_predicate(sub, s.subrange(idx, s.len() as int))) == is_substring_predicate(sub, s) by {
                // This is a direct consequence of the definition
            }
        }
    }

    max_len = 0;
    while (max_len < min_possible_len)
        invariant 
            0 <= max_len as int <= min_possible_len as int,
            forall|k_inv: int| max_len < k_inv as int <= min_possible_len as int ==> !have_common_k_substring_predicate(k_inv as nat, str1, str2),
        decreases min_possible_len - max_len,
    {
        let k = min_possible_len - max_len;

        // Check if there is a common substring of length k
        let mut found_k_common_substring: bool = false;
        let mut i: usize = 0;
        
        while (i <= str1.len() - k)
            invariant 
                0 <= i as int <= str1.len() - k + 1,
                !found_k_common_substring, 
                forall|i_prime: int| 0 <= i_prime < i ==> 
                    forall|j_prime: int| 0 <= j_prime <= str2.len() - k ==> 
                        str1.subrange(i_prime, (i_prime + k) as int) != str2.subrange(j_prime, (j_prime + k) as int),
            decreases str1.len() - k - i,
        {
            let mut j: usize = 0;
            while (j <= str2.len() - k)
                invariant
                    0 <= j as int <= str2.len() - k + 1,
                    !found_k_common_substring,
                    forall|i_prime: int| 0 <= i_prime <= i ==> 
                        forall|j_prime: int| (i_prime == i && 0 <= j_prime < j) || i_prime < i ==> 
                            str1.subrange(i_prime, (i_prime + k) as int) != str2.subrange(j_prime, (j_prime + k) as int),
                decreases str2.len() - k - j,
            {
                if str1.subrange(i as int, (i + k) as int) == str2.subrange(j as int, (j + k) as int) {
                    found_k_common_substring = true;
                    max_len = k; // Update max_len as we found a longer one
                    // Set j and i to values that terminate the loops
                    j = str2.len() - k + 1; 
                    i = str1.len() - k + 1; 
                } else {
                    j = j + 1;
                }
            }
            if !found_k_common_substring {
                i = i + 1;
            }
        }
        if found_k_common_substring {
            return max_len;
        } else {
            // max_len remains unchanged. Loop continues to check smaller k
            // The value of k in this iteration (min_possible_len - max_len)
            // is not a common substring length.
            // When !found_k_common_substring, means
            // forall|i,j| str1.subrange(i,i+k) != str2.subrange(j,j+k)
            // so !have_common_k_substring_predicate(k as nat, str1, str2) is true.
        }
    }
    
    max_len
}
// </vc-code>

fn main() {}

}