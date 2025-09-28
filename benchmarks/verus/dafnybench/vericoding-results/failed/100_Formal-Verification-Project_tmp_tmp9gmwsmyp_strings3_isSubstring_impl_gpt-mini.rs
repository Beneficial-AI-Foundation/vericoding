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
// <vc-helpers>
/* Helper proofs (none required beyond what is in the implementation). */
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> is_substring_pred(sub, str)
    //ensures !res <==> is_not_substring_pred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if sub.len() > str.len() {
        proof {
            // If sub is longer than str, then for every suffix of str, sub.len() > suffix.len(),
            // hence is_not_prefix_pred(sub, suffix) holds for all suffixes, so sub is not a substring.
            assert(forall|i: int|
                0 <= i && i <= str.len() ==>
                    sub.len() > (str.len() - i) || sub != str.subrange(i, i + sub.len())
            );
            assert(forall|i: int|
                0 <= i && i <= str.len() ==>
                    is_not_prefix_pred(sub, str.subrange(i, str.len()))
            );
            // Therefore is_substring_pred(sub, str) is false.
        }
        return false;
    }

    let max_start: int = str.len() - sub.len();

    let mut i: int = 0;
    while i <= max_start {
        invariant 0 <= i;
        invariant i <= max_start + 1;
        invariant forall|j: int| 0 <= j && j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len()));
        // check whether sub is a prefix of str.subrange(i, str.len())
        let mut j: int = 0;
        let mut matched: bool = true;
        while j < sub.len() {
            invariant 0 <= j && j <= sub.len();
            invariant matched ==> forall|k: int| 0 <= k && k < j ==> str@[i + k] == sub@[k];
            if str@[i + j] != sub@[j] {
                matched = false;
            } else {
                j = j + 1;
            }
        }
        if matched {
            proof {
                // On exit from inner loop with matched == true, we must have j == sub.len()
                // because loop condition is j < sub.len() and invariant 0 <= j <= sub.len().
                assert(j == sub.len());
                // Also i is within 0..=max_start because outer loop condition ensures that.
                assert(0 <= i && i <= max_start);
                // Therefore sub.len() <= str.len() - i, i.e., sub fits in the suffix.
                assert(sub.len() <= str.subrange(i, str.len()).len());
                // From the inner-loop invariant with j == sub.len(), we get equality of all characters.
                assert(forall|k: int| 0 <= k && k < sub.len() ==> str@[i + k] == sub@[k]);
                // Thus sub equals the prefix of the suffix starting at i, so is_prefix_pred holds.
                assert(is_prefix_pred(sub, str.subrange(i, str.len())));
            }
            return true;
        }

        i = i + 1;
    }

    proof {
        // After the loop, i == max_start + 1 and we have
        // forall j 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len()))
        assert(i == max_start + 1);
        assert(forall|j: int| 0 <= j && j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len())));

        // We need to show forall q: 0 <= q <= str.len() ==> is_not_prefix_pred(sub, str.subrange(q, str.len()))
        // Consider any q in 0..=str.len().
        assert(forall|q: int| 0 <= q && q <= str.len() ==>
            {
                if q <= max_start {
                    // For q <= max_start we have it from the loop invariant (since q < i).
                    is_not_prefix_pred(sub, str.subrange(q, str.len()))
                } else {
                    // For q > max_start, sub.len() > str.len() - q, so the first disjunct of is_not_prefix_pred holds.
                    is_not_prefix_pred(sub, str.subrange(q, str.len()))
                }
            }
        );
        // Justify the second branch: if q >= max_start + 1 then q > max_start, so str.len() - q < sub.len()
        assert(forall|q: int| max_start + 1 <= q && q <= str.len() ==>
            sub.len() > (str.len() - q)
        );
        // Combine to conclude that sub is not a substring of str.
        assert(forall|q: int| 0 <= q && q <= str.len() ==> is_not_prefix_pred(sub, str.subrange(q, str.len())));
    }

    return false;
}
// </vc-code>

fn main() {}

}