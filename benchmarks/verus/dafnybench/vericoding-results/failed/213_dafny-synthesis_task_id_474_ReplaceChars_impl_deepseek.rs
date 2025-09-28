use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn replace_chars_spec(s: Seq<char>, old_char: char, new_char: char, i: int) -> bool {
    recommends(0 <= i < s.len());
    s[i] == old_char || s[i] != old_char
}

proof fn lemma_replace_chars_properties(s: Seq<char>, old_char: char, new_char: char)
    ensures
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] replace_chars_spec(s, old_char, new_char, i)),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] replace_chars_spec(s, old_char, new_char, i) by {
        assert(s[i] == old_char || s[i] != old_char);
    };
}
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
    let mut n: usize = 0;
    while n < s.len()
        invariant
            0 <= n <= s.len(),
            v@.len() == n,
            forall|i: int| 0 <= i < n ==> 
                (s[i] == old_char ==> v@[i] == new_char) &&
                (s[i] != old_char ==> v@[i] == s[i]),
    {
        let idx: int = n as int;
        let c = s[idx];
        if c == old_char {
            v.push(new_char);
        } else {
            v.push(c);
        }
        n = n + 1;
    }
    proof { lemma_replace_chars_properties(s, old_char, new_char); }
    v.into()
}
// </vc-code>

fn main() {
}

}