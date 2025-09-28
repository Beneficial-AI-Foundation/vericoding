use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
fn replace_blanks_with_char(s: &[char], ch: char) -> (v: Seq<char>)
    ensures 
        v.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            (s@[i] == ' ' ==> v[i] == ch) &&
            (s@[i] != ' ' ==> v[i] == s@[i])
{
    let mut result: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    while idx < s.len()
        invariant
            0 <= idx && idx <= s.len(),
            result@.len() == idx,
            forall|j: int| 0 <= j < idx ==> 
                (s@[j] == ' ' ==> result@[j] == ch) &&
                (s@[j] != ' ' ==> result@[j] == s@[j])
    {
        if s[idx] == ' ' {
            result.push(ch);
        } else {
            result.push(s[idx]);
        }
        idx += 1;
    }
    let v = result@;
    v
}
// </vc-code>

fn main() {}

}