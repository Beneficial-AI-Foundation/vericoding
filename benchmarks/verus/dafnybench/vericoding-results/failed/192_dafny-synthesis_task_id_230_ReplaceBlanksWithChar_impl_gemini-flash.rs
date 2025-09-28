use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_blank(c: char) -> bool {
    c == ' '
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
    let mut v: Vec<char> = Vec::new();
    let s_len = s.len();

    // Initialize v with the same length as s. This is a common pattern for building
    // a new sequence from an existing one in Verus.
    // We'll fill it with dummy data first, and then replace it.
    // Verus requires vectors to be fully initialized.
    let mut i: usize = 0;
    while i < s_len
        invariant
            i <= s_len,
            v.len() == i,
    {
        v.push('a'); // Push a dummy character to pre-allocate
        i = i + 1;
    }
    proof {
        assert(v.len() == s_len);
    }

    let mut i: usize = 0;
    while i < s_len
        invariant
            i <= s_len,
            v.len() == s_len,
            forall|j: int| 0 <= j && (j as usize) < i ==> {
                (s[j] == ' ' ==> v@[j as usize] == ch) &&
                (s[j] != ' ' ==> v@[j as usize] == s[j])
            },
    {
        let current_char = s[i as int];
        if is_blank(current_char) {
            v.set(i, ch);
        } else {
            v.set(i, current_char);
        }
        i = i + 1;
    }

    v.to_seq()
}
// </vc-code>

fn main() {}

}