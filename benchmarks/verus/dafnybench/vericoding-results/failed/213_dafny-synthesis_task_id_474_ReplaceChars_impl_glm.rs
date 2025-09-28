use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace_chars(s: Seq<char>, old_char: char, new_char: char) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i]),
// </vc-spec>
// <vc-code>
{
    Seq::new(s.len(), |i: int| 
        if s[i] == old_char { new_char } else { s[i] }
    )
}
// </vc-code>

fn main() {
}

}