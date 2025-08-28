use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn replace_chars(s: Seq<char>, old_char: char, new_char: char) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i]),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn replace_chars(s: Seq<char>, old_char: char, new_char: char) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i]),
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                (s[k] == old_char ==> result[k as usize] == new_char) &&
                (s[k] != old_char ==> result[k as usize] == s[k]),
    {
        let ch = s[i as int];
        if ch == old_char {
            result.push(new_char);
        } else {
            result.push(ch);
        }
        i = i + 1;
    }

    result.into_seq()
}
// </vc-code>

fn main() {
}

}