use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: int = s.len() as int;
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant result.len() == (i as nat);
        invariant forall |j: int| 0 <= j && j < i ==> result[j] == (if s[j] == old { new } else { s[j] });
        decreases n - i
    {
        let ch: char = s[i as usize];
        let rch: char = if ch == old { new } else { ch };
        result.push(rch);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}