use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut v = Seq::<char>::empty();
    let mut i: nat = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (s[j] == ' ' ==> v[j] == ch) &&
                (s[j] != ' ' ==> v[j] == s[j])
            }
    {
        if s[i as int] == ' ' {
            v = v.push(ch);
        } else {
            v = v.push(s[i as int]);
        }
        i = i + 1;
    }
    
    v
}
// </vc-code>

fn main() {}

}