use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
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
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len() {
        invariant {
            result.len() == i && forall |j: int| 0 <= j && j < i ==> result[j] == (if s[j] == old { new } else { s[j] })
        }
        if s[i] == old {
            result.push(new);
        } else {
            result.push(s[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}