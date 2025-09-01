use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn replace_chars_spec(s: Seq<char>, old: char, new: char) -> Seq<char>
	ensures
		result@.len() == s@.len(),
		forall|i: int| 0 <= i && i < result@.len() ==> result@[i] == (if s@[i] == old { new } else { s@[i] }),
{ unimplemented!() }
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
fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == (if s@[i] == old { new } else { s@[i] }),
{
    let mut result: Vec<char> = Vec::new();
    let slen = s.len();
    proof {
        assert(s@.len() == slen as nat);
    }
    let mut i: usize = 0;
    while i < slen
        invariant
            0 <= i && i <= slen as nat,
            i <= s@.len(),
            result@.len() == i as nat,
            forall|j: int| 0 <= j && j < i as int ==> result@[j] == (if s@[j] == old { new } else { s@[j] }),
    {
        let ch = s[i];
        let to_push = if ch == old { new } else { ch };
        result.push(to_push);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}