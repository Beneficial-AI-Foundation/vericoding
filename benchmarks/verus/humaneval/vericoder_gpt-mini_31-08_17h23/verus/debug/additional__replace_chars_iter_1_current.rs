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
    // impl-start
    let n: int = s.len();
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (if s[j] == old { new } else { s[j] }),
    {
        let c: char = s[i];
        if c == old {
            result.push(new);
        } else {
            result.push(c);
        }
        // establish the invariant for the newly pushed element
        assert(result[i] == (if s[i] == old { new } else { s[i] }));
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}