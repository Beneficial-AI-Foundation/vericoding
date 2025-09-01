use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::string::StrSlice;

// Helper function to check if a substring exists within a string
// In a real scenario, this would likely be part of a string library.
// For this problem, we'll demonstrate a basic implementation.
// This function needs to be a `spec` function to be used in quantifiers.
verus! {
    // We can't use `fndecl!` to declare standalone functions like this.
    // Instead, define it as a public `spec` function.
    pub open spec fn contains_substring(s: StrSlice, sub: StrSlice) -> bool {
        sub.len() == 0 || (
            exists |i: int| #[trigger] s.subrange(i, (i + sub.len())) == sub
            && 0 <= i && i + sub.len() <= s.len()
        )
    }
}
// </vc-helpers>

// <vc-spec>
fn filter_by_substring<'a>(strings: &Vec<&'a str>, substring: &str) -> (res: Vec<&'a str>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < strings@.len() && (exists|j: int|
                0 <= j <= strings@[i]@.len() - substring@.len() && strings[i]@.subrange(
                    j,
                    #[trigger] (j + substring@.len()),
                ) == substring@) ==> res@.contains(#[trigger] (strings[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res_vec = Vec::new();
    let mut i: int = 0;

    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            res_vec.len() <= strings.len(),
            forall|k: int|
                0 <= k < i && contains_substring(strings@[k], substring@)
                ==> res_vec@.contains(#[trigger] (strings[k])),
            // The elements already in res_vec must have come from strings[0..i-1] satisfying the condition
            forall|k: int|
                0 <= k < res_vec.len() ==> (
                    exists|idx: int|
                        0 <= idx < i && res_vec@[k] == strings@[idx] &&
                        contains_substring(strings@[idx], substring@)
                ),
    {
        let current_string = strings@[i];
        let mut found = false;
        let mut j: int = 0;

        proof {
            assert(current_string@.len() >= 0);
            assert(substring@.len() >= 0);
        }

        while !found && j + substring@.len() <= current_string@.len()
            invariant
                0 <= j <= current_string@.len(),
                found ==> (
                    j + substring@.len() <= current_string@.len() &&
                    current_string@.subrange(j - substring@.len(), j) == substring@
                ), // If found, the current j is past the start of the substring
                !found ==> (
                    forall|k: int|
                        0 <= k < j ==> current_string@.subrange(k, (k + substring@.len())) != substring@
                ),
                current_string@.len() >= substring@.len() || substring@.len() == 0,
        {
            if current_string@.subrange(j, (j + substring@.len())) == substring@ {
                found = true;
            }
            j = j + 1;
        }

        if found {
            res_vec.push(current_string);
        } else if substring@.len() == 0 {
            // A zero-length substring is contained in every string
            res_vec.push(current_string);
        }

        proof {
            // Prove that if `found` is true, then current_string contains substring
            // Or if substring is empty, it contains it vacuously.
            if found {
                assert(contains_substring(current_string, substring@));
            } else if substring@.len() == 0 {
                assert(contains_substring(current_string, substring@));
            } else {
                assert(current_string@.len() < substring@.len() || (forall |k: int| 0 <= k < j ==>
                    current_string@.subrange(k, k + substring@.len()) != substring@));
                assert(j + substring@.len() > current_string@.len());

                // If substring@.len() > current_string@.len(), then it cannot be contained unless substring is empty.
                if current_string@.len() < substring@.len() {
                    assert(!contains_substring(current_string, substring@));
                } else {
                    // If not found and substring is not empty, then it does not contain it
                    assert(!(exists|k: int|
                        0 <= k && k + substring@.len() <= current_string@.len() &&
                        current_string@.subrange(k, (k + substring@.len())) == substring@
                    )) by {
                        assert(forall|k: int|
                            0 <= k < j ==> current_string@.subrange(k, (k + substring@.len())) != substring@
                        );
                        assert(j + substring@.len() > current_string@.len()); // j must run out of bounds or find something
                        if current_string@.len() >= substring@.len() { // Only need to check if current_string is long enough for substring
                            assert(forall|k: int|
                                0 <= k <= current_string@.len() - substring@.len() ==> current_string@.subrange(k, (k+substring@.len())) != substring@
                            );
                        }
                    };
                    assert(!contains_substring(current_string, substring@));
                }
            }
        }
        i = i + 1;
    }

    // Now, prove the postcondition
    proof {
        assert forall|k: int|
            0 <= k < strings@.len() && contains_substring(strings@[k], substring@)
            implies res_vec@.contains(#[trigger] (strings[k])) by {

            // We need to show that if strings[k] satisfies the condition, it was added to res_vec.
            // When `i` reached `k+1`, the inner loop correctly determined if `strings[k]` contained `substring`.
            // The `if found { res_vec.push(current_string); } else if substring@.len() == 0 { ... }` ensures this.

            // The invariant on `i` ensures:
            // forall|x: int|
            //     0 <= x < i && (
            //         exists|j: int|
            //             0 <= j <= strings@[x]@.len() - substring@.len() && strings[x]@.subrange(j, (j + substring@.len())) == substring@
            //     ) ==> res_vec@.contains(#[trigger] (strings[x]))
            // At the end, i is strings.len(), so this applies for all 0 <= x < strings.len().

            // Specifically, for the given k:
            let string_at_k = strings@[k];
            assert(contains_substring(string_at_k, substring@)); // from the premise of the ensures clause
            assert(k < i); // since k ranges from 0 to strings@.len()-1 and i is strings@.len()
            assert(res_vec@.contains(string_at_k)); // from the loop invariant.
        }
    }
    res_vec
}
// </vc-code>

fn main() {}
}