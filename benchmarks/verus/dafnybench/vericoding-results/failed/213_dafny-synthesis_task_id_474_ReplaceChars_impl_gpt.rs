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
    let v = Seq::new(s.len(), |i: int| if s.index(i) == old_char { new_char } else { s.index(i) });
    assert(v.len() == s.len());
    proof {
        assert_forall_by(|i: int| {
            requires(0 <= i && i < s.len());
            ensures(
                (s[i] == old_char ==> v[i] == new_char) &&
                (s[i] != old_char ==> v[i] == s[i])
            );
            assert(0 <= i && i < v.len());
            if s[i] == old_char {
                assert(v[i] == new_char);
            } else {
                assert(v[i] == s[i]);
            }
        });
        assert(forall|i: int| 0 <= i && i < s.len() ==>
            (s[i] == old_char ==> v[i] == new_char) &&
            (s[i] != old_char ==> v[i] == s[i])
        );
    }
    v
}
// </vc-code>

fn main() {
}

}