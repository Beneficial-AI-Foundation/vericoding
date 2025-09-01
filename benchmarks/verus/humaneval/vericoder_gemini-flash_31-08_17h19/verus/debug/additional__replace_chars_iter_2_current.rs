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

    // Loop invariant:
    // 1. `result.len()` is equal to `i`
    // 2. For all `k` from 0 to `i-1`, `result[k]` is the replacement of `s[k]`
    // 3. `result` has sufficient capacity (this is handled by `push_unchecked` if capacity is given beforehand, but here `push` handles it safely)
    let mut i = 0;
    while i < old_len
        invariant
            i <= old_len,
            result.len() == i,
            forall|k: int| 0 <= k && k < i ==> result.view_nth(k) == (if s.view_nth(k) == old { new } else { s.view_nth(k) }),
        decreases old_len - i
    {
        let char_to_add = if s[i] == old { new } else { s[i] };
        result.push(char_to_add);

        i = i + 1;
    }

    assert(result.len() == old_len);
    assert(forall|j: int| 0 <= j && j < result.len() ==> result.view_nth(j) == (if s.view_nth(j) == old { new } else { s.view_nth(j) }));

    result
}
// </vc-code>

fn main() {}
}