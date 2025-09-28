use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn replace_blanks_preserves_length(s: Seq<char>, ch: char) 
    ensures 
        replace_blanks_with_char(s, ch).len() == s.len()
{
}

proof fn replace_blanks_correctness(s: Seq<char>, ch: char, i: int)
    requires
        0 <= i < s.len()
    ensures 
        (s[i] == ' ' ==> replace_blanks_with_char(s, ch)[i] == ch) &&
        (s[i] != ' ' ==> replace_blanks_with_char(s, ch)[i] == s[i])
{
}
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
    let mut v = Vec::<char>::new();
    let len = s.len();
    let mut index: usize = 0;
    while index < len
        invariant
            0 <= index <= len,
            v@.len() == index,
            forall|j: int| 0 <= j < index ==> {
                (s[j] == ' ' ==> v@[j] == ch) &&
                (s[j] != ' ' ==> v@[j] == s[j])
            }
    {
        if s[index as int] == ' ' {
            v.push(ch);
        } else {
            v.push(s[index as int]);
        }
        index = index + 1;
    }
    v.into()
}
// </vc-code>

fn main() {}

}