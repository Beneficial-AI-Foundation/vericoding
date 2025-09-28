use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn replace_blanks_with_char(s: Seq<char>, ch: char) -> (v: Seq<char>)
    ensures 
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            (s[i] == ' ' ==> v[i] == ch) &&
            (s[i] != ' ' ==> v[i] == s[i])
        }
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<char> = Vec::new();
    let mut i: int = 0;
    while (i < s.len())
        invariant 0 <= i && i <= s.len();
        invariant v@.len() == i as nat;
        invariant forall |j: int| 0 <= j && j < i ==>
            ((s[j] == ' ' ==> v@[j as nat] == ch) &&
             (s[j] != ' ' ==> v@[j as nat] == s[j]));
    {
        let c: char = s[i];
        if c == ' ' {
            v.push(ch);
        } else {
            v.push(c);
        }
        i = i + 1;
    }
    v.into_seq()
}
// </vc-code>

fn main() {}

}