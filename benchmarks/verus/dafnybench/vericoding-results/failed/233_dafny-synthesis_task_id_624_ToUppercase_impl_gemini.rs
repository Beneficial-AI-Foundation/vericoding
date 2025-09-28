// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected paths to standard library lemmas. */
proof fn lemma_shift_is_upper(c: char)
    requires
        is_lower_case(c),
    ensures
        is_lower_upper_pair(c, shift_minus_32(c)),
{
    let shifted_val = c as int - 32;
    vstd::arithmetic::mod_p::lemma_mod_of_nonneg(shifted_val, 128);
    vstd::string::lemma_int_as_char_id(shifted_val);
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
    /* code modified by LLM (iteration 5): This implementation is correct; it should verify with the fixed helper lemma. */
    let v = s.map(|_i: int, c: char|
        if is_lower_case(c) {
            shift_minus_32(c)
        } else {
            c
        }
    );

    assert forall|i: int| 0 <= i < s.len() implies
        if is_lower_case(s[i]) {
            is_lower_upper_pair(s[i], v[i])
        } else {
            v[i] == s[i]
        }
    by {
        if is_lower_case(s[i]) {
            lemma_shift_is_upper(s[i]);
        }
    };
    v
}
// </vc-code>

}
fn main() {}