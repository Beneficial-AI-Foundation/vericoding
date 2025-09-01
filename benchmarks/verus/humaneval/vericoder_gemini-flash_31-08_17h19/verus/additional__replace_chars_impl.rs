use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if s[i] == old { new } else { s[i] }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let old_len = s.len();

    let mut i = 0;
    while i < old_len
        invariant
            i <= old_len,
            result.len() == i,
            forall|k: int| 0 <= k && k < i ==> #[trigger] result.view()[k] == (if s.view()[k] == old { new } else { s.view()[k] }),
            s.len() == old_len, // Add this invariant to ensure s is not modified and its length is consistent
        decreases old_len - i
    {
        // Prove that s[i] is safe to access inside the loop
        proof {
            assert(i < s.len());
        }
        let char_to_add = if s[i] == old { new } else { s[i] };
        result.push(char_to_add);

        i = i + 1;
    }

    assert(result.len() == old_len);
    assert(forall|j: int| 0 <= j && j < result.len() ==> #[trigger] result.view()[j] == (if s.view()[j] == old { new } else { s.view()[j] }));

    result
}
// </vc-code>

fn main() {}
}