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
    let mut result = Seq::<char>::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (s[j] == old_char ==> result[j] == new_char) &&
                (s[j] != old_char ==> result[j] == s[j]),
    {
        if s[i as int] == old_char {
            result = result.push(new_char);
        } else {
            result = result.push(s[i as int]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}