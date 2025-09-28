use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this implementation
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
    let v = s.map_values(|c: char| -> char {
        if c == old_char { new_char } else { c }
    });
    
    // Prove the postconditions
    assert forall|i: int| 0 <= i < s.len() implies {
        let mapped = if s[i] == old_char { new_char } else { s[i] };
        v[i] == mapped
    } by {
        assert(v[i] == (if s[i] == old_char { new_char } else { s[i] }));
    }
    
    assert forall|i: int| 0 <= i < s.len() implies 
        (s[i] == old_char ==> v[i] == new_char) &&
        (s[i] != old_char ==> v[i] == s[i]) by {
        assert(v[i] == (if s[i] == old_char { new_char } else { s[i] }));
    }
    
    v
}
// </vc-code>

fn main() {
}

}