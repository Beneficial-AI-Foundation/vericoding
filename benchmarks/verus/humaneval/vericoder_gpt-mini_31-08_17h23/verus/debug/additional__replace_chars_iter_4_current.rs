use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let n: usize = s.len();
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==>
                result[j] == (if s[j as usize] == old { new } else { s[j as usize] }),
    {
        let c: char = s[i];
        if c == old {
            result.push(new);
        } else {
            result.push(c);
        }
        assert(result[i as int] == (if s[i] == old { new } else { s[i] }));
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}