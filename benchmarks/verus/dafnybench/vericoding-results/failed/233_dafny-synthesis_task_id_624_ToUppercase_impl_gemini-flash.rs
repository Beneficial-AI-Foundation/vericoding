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
#[verifier(external_body)]
proof fn lemma_char_int_in_range(c: char)
    ensures
        0 <= c as int < 128,
{}

#[verifier(external_body)]
proof fn lemma_char_from_int(i: int)
    requires
        0 <= i < 128,
    ensures
        (i as char) as int == i,
{}

proof fn lemma_char_ops(c: char)
    requires
        is_lower_case(c),
    ensures
        is_lower_upper_pair(c, shift_minus_32(c)),
{
    reveal(shift_minus_32);
    reveal(is_lower_upper_pair);
    reveal(is_lower_case);
    lemma_char_int_in_range(c);
    let c_int = c as int;
    let C_int = c_int - 32;
    assert(C_int == (c as int) - 32);
    assert(c_int >= 97);
    assert(c_int <= 122);
    assert(C_int >= 65);
    assert(C_int <= 90);
    assert(0 <= C_int < 128);
    lemma_char_from_int(C_int);
}
// </vc-helpers>

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
// <vc-code>
{
    let mut v: Seq<char> = Seq::empty(); // Initialize v as an empty sequence
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==>
                #[trigger] v[j];
                if is_lower_case(s[j]) {
                    is_lower_upper_pair(s[j], v[j])
                } else {
                    v[j] == s[j]
                },
    {
        let current_char = s[i];
        if is_lower_case(current_char) {
            lemma_char_ops(current_char);
            v = v.snoc(shift_minus_32(current_char));
        } else {
            v = v.snoc(current_char);
        }
        i = i + 1;
    }
    v
}
// </vc-code>

fn main() {
}

}