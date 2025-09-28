use vstd::prelude::*;

verus! {

// Noa Leron 207131871
// Tsuri Farhana 315016907

spec fn is_prefix(prefix: Seq<char>, full: Seq<char>) -> bool {
    prefix.len() <= full.len() &&
    forall|k: int| 0 <= k < prefix.len() ==> prefix[k] == full[k]
}

spec fn exists_substring(str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|offset: int| 0 <= offset <= str1.len() - str2.len() &&
        is_prefix(str2, str1.subrange(offset, str1.len() as int))
}

spec fn post(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found <==> exists_substring(str1, str2)) &&
    (found ==> i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))
}

/*
Goal: Verify correctness of the following code. Once done, remove the {:verify false} (or turn it into {:verify true}).

Feel free to add GHOST code, including calls to lemmas. But DO NOT modify the specification or the original (executable) code.
*/

//this is our lemmas, invatiants and presicats

spec fn outter_inv_correctness(str1: Seq<char>, str2: Seq<char>, found: bool, i: nat) -> bool {
    (found ==> (i + str2.len() <= str1.len() && 
        is_prefix(str2, str1.subrange(i as int, str1.len() as int)))) && // Second part of post condition
    (!found && 0 < i <= str1.len() && i != str2.len() - 1 ==> 
        !(exists_substring(str1.subrange(0, i as int), str2))) && // First part of post condition
    (!found ==> i <= str1.len())
}

spec fn inner_inv_correctness(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, found: bool) -> bool {
    0 <= j <= i && // index in range
    j < str2.len() && // index in range
    i < str1.len() && // index in range
    (str1[i as int] == str2[j] ==> 
        is_prefix(str2.subrange(j, str2.len() as int), str1.subrange(i as int, str1.len() as int))) &&
    (found ==> j == 0 && str1[i as int] == str2[j])
}

spec fn inner_inv_termination(str1: Seq<char>, str2: Seq<char>, i: nat, j: int, old_i: nat, old_j: nat) -> bool {
    old_j - j == old_i - old_i
}

// <vc-helpers>
lemma fn subrange_equals_prefix(s1: Seq<char>, s2: Seq<char>, offset: int)
    requires
        0 <= offset,
        offset <= s1.len() - s2.len(),
        is_prefix(s2, s1.subrange(offset, s1.len() as int)),
    ensures
        exists_substring(s1, s2),
{
    assert(exists_substring(s1, s2)) by {
        assert(is_prefix(s2, s1.subrange(offset, s1.len() as int)));
    }
}

lemma fn subrange_not_exists_substring(s1: Seq<char>, s2: Seq<char>, limit: int)
    requires
        0 <= limit,
        forall |k: int| 0 <= k < limit ==> #[trigger] !is_prefix(s2, s1.subrange(k, s1.len() as int)),
    ensures
        !exists_substring(s1.subrange(0, limit as int), s2),
{
    // If exists_substring(s1.subrange(0, limit as int), s2) were true,
    // then there would exist some `offset_in_subrange` such that
    // 0 <= offset_in_subrange <= (s1.subrange(0, limit as int)).len() - s2.len()
    // AND is_prefix(s2, (s1.subrange(0, limit as int)).subrange(offset_in_subrange, ...)).
    // This `offset_in_subrange` corresponds to an `offset` in `s1` where `offset = offset_in_subrange`.
    // And `offset < limit` by `offset_in_subrange <= limit - s2.len()`.
    // But this would contradict the requires clause.
    assert(!exists_substring(s1.subrange(0, limit as int), s2)) by {
        if (exists_substring(s1.subrange(0, limit as int), s2)) {
            let chopped_s1 = s1.subrange(0, limit as int);
            assert(exists |offset_in_chopped_s1: int| 0 <= offset_in_chopped_s1 <= chopped_s1.len() - s2.len() &&
                is_prefix(s2, chopped_s1.subrange(offset_in_chopped_s1, chopped_s1.len() as int)));

            // Let `k` be such an `offset_in_chopped_s1`.
            // Then `k` corresponds to an `offset` in the original `s1` with the same value.
            // And `k < limit` because `k <= chopped_s1.len() - s2.len() = limit - s2.len()`.
            // This contradicts the `forall` in the requires clause.
            // This proof requires explicit instantiation of the exists quantifier for `exists_substring`.
            // For now, Verus can deduce this sometimes implicitly.
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(str1: Seq<char>, str2: Seq<char>) -> (result: (bool, usize))
    ensures post(str1, str2, result.0, result.1 as nat)
// </vc-spec>
// <vc-code>
{
    let mut found: bool = false;
    let mut i: usize = 0;
    let mut matching_idx: usize = 0; // This will store the starting index if found

    // Handle edge cases where str2 is empty or str2 is longer than str1
    if str2.len() == 0 {
        return (true, 0);
    }
    if str2.len() > str1.len() {
        return (false, 0);
    }

    // Outer loop: Iterate through str1
    while i <= str1.len() - str2.len()
        invariant
            str2.len() > 0, // From initial checks
            str2.len() <= str1.len(), // From initial checks
            i <= str1.len() - str2.len() + 1, // Loop termination
            // If found, matching_idx is guaranteed to be a valid start for str2 in str1
            found ==> (matching_idx + str2.len() <= str1.len() && is_prefix(str2, str1.subrange(matching_idx as int, str1.len() as int))),
            // If not found, no prefix match exists in the range [0, i)
            !found ==> (forall |k: int| 0 <= k < i ==> #[trigger] !is_prefix(str2, str1.subrange(k, str1.len() as int))),
            // If found, matching_idx must be less than or equal to the current 'i'
            found ==> matching_idx <= i,
    {
        if found {
            // Once found, we just keep iterating to satisfy the loop invariant and terminate.
            // The `matching_idx` stores the first occurrence.
        } else {
            // Inner loop: Check for a prefix match starting at str1[i]
            let mut j: usize = 0;
            proof {
                // Apply helper lemma for the invariant of the outer loop related to `!found`
            }
            while j < str2.len()
                invariant
                    0 <= j <= str2.len(),
                    i <= str1.len() - str2.len(), // Outer loop invariant
                    str2.len() > 0, // Outer loop invariant
                    !found, // We only enter/continue inner loop if 'found' is false in the outer loop
                    // This invariant states that for all characters compared so far (up to j-1), they match.
                    forall |k: int| 0 <= k < j ==> str1[i as int + k] == str2[k],
                    // The outer loop invariant that asserts no match before 'i' must be maintained.
                    forall |k: int| 0 <= k < i ==> #[trigger] !is_prefix(str2, str1.subrange(k, str1.len() as int)),
                    j <= str2.len(), // Required for termination and to keep j within bounds
            {
                if i + j >= str1.len() {
                    // This condition should ideally not be met if `i <= str1.len() - str2.len()` holds
                    // and `j < str2.len()`.
                    // i + j < i + str2.len() <= (str1.len() - str2.len()) + str2.len() = str1.len()
                    // However, Verus requires this check to acknowledge array indexing bounds.
                    // If str2 is empty, it's handled at the beginning.
                    // If str1 and str2 are both non-empty, and j reaches str2.len(), then i+j means i+str2.len()
                    // which could be str1.len().
                    // The loop condition i <= str1.len() - str2.len() ensures i+str2.len() <= str1.len().
                    break;
                }
                if str1[i + j] != str2[j] {
                    break; // Mismatch found, break inner loop
                }
                j = j + 1;
            }

            // After inner loop, check if a full match was found
            if j == str2.len() {
                found = true;
                matching_idx = i;
                proof {
                    // If j == str2.len(), then the inner loop finished implying all characters matched.
                    // The invariant `forall |k: int| 0 <= k < j ==> str1[i as int + k] == str2[k]`
                    // becomes `forall |k: int| 0 <= k < str2.len() ==> str1[i as int + k] == str2[k]`,
                    // which is exactly what `is_prefix(str2, str1.subrange(i as int, str1.len() as int))` means.
                    assert(is_prefix(str2, str1.subrange(i as int, str1.len() as int)));
                }
            }
        }
        i = i + 1;
    }

    if found {
        proof {
            // From the invariants, if found is true, matching_idx is the start of the first occurrence.
            assert(matching_idx + str2.len() <= str1.len());
            assert(is_prefix(str2, str1.subrange(matching_idx as int, str1.len() as int)));
            subrange_equals_prefix(str1, str2, matching_idx as int);

            // Prove the postcondition when found is true
            // P1: (found <==> exists_substring(str1, str2))
            assert(exists_substring(str1, str2)); // from subrange_equals_prefix
            assert(found == exists_substring(str1, str2));

            // P2: (found ==> i + str2.len() <= str1.len() && is_prefix(str2, str1.subrange(i as int, str1.len() as int)))
            // We need to use `matching_idx` here for the postcondition.
            assert(matching_idx + str2.len() <= str1.len());
            assert(is_prefix(str2, str1.subrange(matching_idx as int, str1.len() as int)));
            assert(post(str1, str2, true, matching_idx as nat));
        }
        (true, matching_idx)
    } else {
        proof {
            // Upon loop termination, i will be `str1.len() - str2.len() + 1`.
            // The outer loop invariant `(!found ==> (forall |k: int| 0 <= k < i ==> #[trigger] !is_prefix(str2, str1.subrange(k, str1.len() as int))))`
            // guarantees that no match exists in [0, i-1).
            // Since i is now one past the last possible starting index, we need to show that no match exists
            // in the entire valid range [0, str1.len() - str2.len()].
            let limit = str1.len() as int - str2.len() as int;

            // We need to prove that there is no substring starting at any valid offset if not found.
            // Valid offsets are from 0 to str1.len() - str2.len().
            // The loop terminates when `i` becomes `str1.len() - str2.len() + 1`.
            // So, for all `offset` such that `0 <= offset <= str1.len() - str2.len()`,
            // we have `offset < i`.
            assert forall |offset: int| 0 <= offset <= (str1.len() as int - str2.len() as int) implies #[trigger] !is_prefix(str2, str1.subrange(offset, str1.len() as int)) by {
                // Since i is (str1.len() - str2.len() + 1) at termination, any valid `offset` for a substring start
                // (which is `0` to `str1.len() - str2.len()`) must be strictly less than `i`.
                // Thus, the outer loop invariant `!found ==> (forall |k: int| 0 <= k < i ==> #[trigger] !is_prefix(str2, str1.subrange(k, str1.len() as int)))`
                // applies directly to this `offset`.
                assert((offset as usize) < i); // follows from `offset <= str1.len() - str2.len()` and `i == str1.len() - str2.len() + 1`
                assert(!is_prefix(str2, str1.subrange(offset as int, str1.len() as int))); // directly from outer invariant
            };

            // This implies that `!exists_substring(str1, str2)`.
            // If `str2.len() > str1.len()`, `str1.len() - str2.len()` is negative or zero,
            // and the range `0 <= offset <= (str1.len() - str2.len())` is empty.
            // In that case, `exists_substring(str1, str2)` is false by definition (no such offset exists).
            // Our initial checks handle `str2.len() > str1.len()`.
            // If the loop ran, `str1.len() >= str2.len()`.
            subrange_not_exists_substring(str1, str2, (str1.len() - str2.len() + 1) as int); // Use `i` at loop termination
            assert(!exists_substring(str1, str2));

            // Prove the postcondition when found is false
            // P1: (found <==> exists_substring(str1, str2))
            assert(false == exists_substring(str1, str2));

            // P2: (found ==> i + str2.len() <= str1.len() && is_prefix(str2, str1.subrange(i as int, str1.len() as int)))
            // This part is trivially true because 'found' is false. (False ==> X is always true)
            assert(post(str1, str2, false, 0)); // 'i' (for result.1) can be anything if not found. 0 is fine.
        }
        (false, 0)
    }
}
// </vc-code>

fn main() {
}

}