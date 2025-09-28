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
fn have_common_k_substring(k: usize, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures 
        found <==> have_common_k_substring_pred(k as nat, str1, str2),
        !found <==> have_not_common_k_substring_pred(k as nat, str1, str2),
{
    if k == 0 {
        // A common substring of length 0 always exists (empty string)
        true
    } else if k > str1.len() || k > str2.len() {
        // No common substring possible if k is greater than either string's length
        false
    } else {
        let mut i1: usize = 0;
        let mut found_it: bool = false;
        while i1 <= str1.len() - k
            invariant
                0 <= i1,
                i1 <= str1.len() - k + 1,
                found_it <==> (exists|idx: int| 0 <= idx && (idx as usize) < i1 && { #[trigger] is_substring_pred(str1.subrange(idx as int, idx as int + k as int), str2) }),
            decreases str1.len() - k - i1
        {
            let sub = str1.subrange(i1 as int, (i1 + k) as int);
            if is_substring_pred(sub, str2) {
                found_it = true;
                break;
            }
            i1 = i1 + 1;
        }
        found_it
    }
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
    let mut low: usize = 0;
    let mut high: usize = str1.len(); // max possible length of common substring
    let mut ans: usize = 0;

    while low <= high
        invariant
            low <= str1.len() + 1, // low can be str1.len() + 1
            high <= str1.len(),
            ans <= str1.len(),
            high.checked_add(1).unwrap_or(0) >= low, // high + 1 >= low (avoids overflow)
            // if have_common_k_substring(k, str1, str2) is true, then k <= ans or k > high.
            // If have_common_k_substring(k, str1, str2) is false, then k < low or k > high.
            forall|k: nat| #![auto] (k as usize) > ans && (k as usize) <= str1.len() ==> !have_common_k_substring_pred(k, str1, str2),
            forall|k: nat| #![auto] (k as usize) < low ==> !have_common_k_substring_pred(k, str1, str2),
            // if ans is updated, it must be because we found a common substring of length ans
            (ans == 0 || have_common_k_substring_pred(ans as nat, str1, str2)),
            // if we have high == str1.len() and ans is not updated, then no common substring
            // of length str1.len() or greater.  This is a weaker invariant statement that 
            // should not be required here.
            
            // This ensures that the search space is correctly maintained.
            // All lengths k in [0, low-1] are known to NOT have a common substring.
            // All lengths k in [ans+1, str1.len()] are known to NOT have a common substring.
            // A common substring of length 'ans' has been found IF ans > 0.
            // If ans is 0, it means either no common substring exists, or the function has just begun.

            // The value 'ans' holds the maximum 'k' for which have_common_k_substring(k) is true,
            // for all k tested so far.
            // The range [low, high] is the remaining search space.
            // The invariant states that for k in [0, low-1), have_common_k_substring(k) is false.
            // For k in (ans, str1.len()], have_common_k_substring(k) is false (implicitly high is <= str1.len()).
            // This is the core binary search invariant.

    {
        let mid: usize = low + (high - low) / 2;

        if mid == 0 {
            // handle k=0 special case: empty string is always common
            ans = 0; // The problem specifies len as usize, which can be 0.
            // If have_common_k_substring(0, str1, str2) {
            //     ans = 0;
            // } else {
            //     // This branch should ideally not be reachable since have_common_k_substring(0,..) is always true
            //     // If it were false, then the answer would be 0, implying no common substring.
            // }
            break; // No need to search below 0.
        }

        if have_common_k_substring(mid, str1, str2) {
            // A common substring of length `mid` exists.
            // We try to find a longer one.
            ans = mid;
            low = mid + 1;
        } else {
            // No common substring of length `mid` exists.
            // Try a shorter one.
            high = mid - 1;
        }
    }
    ans
}
// </vc-code>

fn main() {
}

}