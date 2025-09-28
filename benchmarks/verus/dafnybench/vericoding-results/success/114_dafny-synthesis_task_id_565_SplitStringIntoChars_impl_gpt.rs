use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_string_into_chars(s: Vec<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[i] == s[i],
// </vc-spec>
// <vc-code>
{
    s
}
// </vc-code>

fn main() {
}

}