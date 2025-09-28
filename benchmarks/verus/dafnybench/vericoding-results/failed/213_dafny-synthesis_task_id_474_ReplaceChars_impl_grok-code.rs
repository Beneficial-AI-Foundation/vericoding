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
    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| #![trigger] 0 <= j < i ==>
                (s[j] == old_char ==> result[j] == new_char) &&
                (s[j] != old_char ==> result[j] == s[j]),
    {
        result = result.push(if s[i] == old_char { new_char } else { s[i] });
        i = i + 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==>
            (s[j] == old_char ==> result[j] == new_char) &&
            (s[j] != old_char ==> result[j] == s[j]));
        assert(result.len() == s.len());
    }
    result
}
// </vc-code>

fn main() {
}

}