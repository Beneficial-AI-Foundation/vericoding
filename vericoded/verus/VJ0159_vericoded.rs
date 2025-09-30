// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn replace_char_val(x: char, old: char, new: char) -> char { if x == old { new } else { x } }
// </vc-helpers>

// <vc-spec>
fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if s[i] == old { new } else { s[i] }),
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<char> = Vec::new();
    v.reserve(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j && j < i ==> v@[j] == (if s[j] == old { new } else { s[j] }),
        decreases s.len() - i
    {
        let c = if s[i] == old { new } else { s[i] };
        v.push(c);
        i += 1;
    }
    v
}
// </vc-code>

}
fn main() {}