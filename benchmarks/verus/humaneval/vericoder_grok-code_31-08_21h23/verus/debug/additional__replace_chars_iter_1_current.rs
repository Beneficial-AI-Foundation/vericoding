use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    let mut result = Vec::with_capacity(s@.len());
    #[verifier::loop_isolation(false)]
    for i in 0..s.len()
    invariant
        i <= s.len(),
        result.len() == i,
        forall |j: int| #![trigger result@[j]] 0 <= j && j < i ==> 
            result@[j] == (if s@[j] == old { new } else { s@[j] })
    {
        let c = s@[i];
        if c == old {
            result.push(new);
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>

fn main() {}
}