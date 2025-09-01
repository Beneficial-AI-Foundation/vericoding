use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a substring exists within a string
// In a real scenario, this would likely be part of a string library.
// For this problem, we'll demonstrate a basic implementation.
// This function needs to be a `spec` function to be used in quantifiers.
verus! {
    // We can't use `fndecl!` to declare standalone functions like this.
    // Instead, define it as a public `spec` function.
    pub open spec fn contains_substring(s: &str, sub: &str) -> bool {
        sub.len() == 0 || (
            exists |i: int| #[trigger] s.substring(i as nat, (i as nat + sub.len() as nat)) == sub
            && 0 <= i && i as nat + sub.len() as nat <= s.len() as nat
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
            res_vec.len() <= i, // This is a tighter bound than strings.len()
            forall|k: int|
                0 <= k < i && contains_substring(strings@[k], substring)
                ==> res_vec@.contains(#[trigger] (strings[k])),
            // The elements already in res_vec must have come from strings[0..i-1] satisfying the condition
            forall|k: int|
                0 <= k < res_vec.len() ==> (
                    exists|idx: int|
                        0 <= idx < i && res_vec@[k] == strings@[idx] &&
                        contains_substring(strings@[idx], substring)
                ),
    {
        let current_string = strings@[i];
        let mut found = false;
        let mut j: int = 0;

        proof {
            assert(current_string.len() >= 0);
            assert(substring.len() >= 0);
        }

        while !found && (j as nat) + (substring.len() as nat) <= (current_string.len() as nat)
            invariant
                0 <= j,
                j as nat <= current_string.len() as nat,
                found ==> (
                    j as nat + substring.len() as nat >= current_string.len() as nat && // j must have advanced past the finding spot
                    current_string.substring((j-1) as nat, (j-1) as nat + substring.len() as nat) == substring // the found substring is at j-1 when found becomes true assuming j is incremented right after
                ),
                !found ==> (
                    forall|k: int|
                        0 <= k < j ==> current_string.substring(k as nat, k as nat + substring.len() as nat) != substring
                ),
                current_string.len() >= 0,
                substring.len() >= 0,
        {
            if (j as nat) + (substring.len() as nat) <= (current_string.len() as nat) {
                if current_string.substring(j as nat, (j as nat + substring.len() as nat)) == substring {
                    found = true;
                }
            }
            j = j + 1;
        }

        // After the loop, if 'found' is true, substring was found; otherwise, it was not.
        // Special case: empty substring is in every string.
        if found {
            res_vec.push(current_string);
            assert(contains_substring(current_string, substring)); // If found, it contains.
        } else if substring.len() == 0 {
            // A zero-length substring is contained in every string
            res_vec.push(current_string); // contains_substring is true for empty substring
            assert(contains_substring(current_string, substring));
        } else {
            // If not found and substring is not empty, then current_string does not contain substring.
            proof {
                assert(!contains_substring(current_string, substring));
            }
        }
        i = i + 1;
    }

    // Now, prove the postcondition
    proof {
        assert forall|k: int|
            0 <= k < strings@.len() && contains_substring(strings@[k], substring)
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
            assert(contains_substring(string_at_k, substring)); // from the premise of the ensures clause
            assert(k < i); // since k ranges from 0 to strings@.len()-1 and i is strings@.len()
            assert(res_vec@.contains(string_at_k)); // from the loop invariant.
        }
    }
    res_vec
}
// </vc-code>

fn main() {}
}