use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

spec fn shift_minus_32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

// <vc-helpers>
spec fn to_uppercase_char(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32(c)
    } else {
        c
    }
}

proof fn lemma_shift_minus_32_correct(c: char)
    requires is_lower_case(c)
    ensures is_lower_upper_pair(c, shift_minus_32(c))
{
    let upper = shift_minus_32(c);
    assert(c as int >= 97 && c as int <= 122);
    assert(upper as int == (c as int - 32) % 128);
    assert(c as int - 32 >= 65 && c as int - 32 <= 90);
    assert(c as int - 32 < 128);
    assert(upper as int == c as int - 32);
    assert((c as int) == (upper as int) + 32);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn to_uppercase(s: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], v[i])
            } else {
                v[i] == s[i]
            }
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    Seq::new(s.len(), |i: int| to_uppercase_char(s[i]))
}
// </vc-code>

fn main() {
}

}