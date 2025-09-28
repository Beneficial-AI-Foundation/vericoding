use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut v: Vec<char> = Vec::new();
    while v.len() < s.len()
        invariant 0 <= v.len() && v.len() <= s.len();
        invariant forall|j: int| 0 <= j && j < v.len() ==>
            (s[j] == old_char ==> v.as_seq()[j] == new_char) &&
            (s[j] != old_char ==> v.as_seq()[j] == s[j]);
        decreases s.len() - v.len();
    {
        let i: int = v.len();
        assert(0 <= i && i < s.len());
        if s[i] == old_char {
            v.push(new_char);
        } else {
            v.push(s[i]);
        }
    }
    v.into_seq()
}
// </vc-code>

fn main() {
}

}