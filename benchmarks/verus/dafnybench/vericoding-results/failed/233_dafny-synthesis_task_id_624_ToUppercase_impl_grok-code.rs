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
#[verifier::proof]
spec fn lemma_lower_shift() 
ensures
    forall| c: char | #[trigger] is_lower_case(c) ==> is_lower_upper_pair(c, shift_minus_32(c))
{
    assert forall | ch: char | is_lower_case(ch) implies is_lower_upper_pair(ch, shift_minus_32(ch)) by {
        assert(97 <= ch as int <= 122);  // from is_lower_case(c)
        let upper_ascii = (ch as int - 32) % 128;
        assert(65 <= upper_ascii <= 90) by {
            // ch as int >=97 => upper >=65, ch as int <=122 => upper <=90
        };
        assert(upper_ascii == (ch as int - 32)) by {
            assert(ch as int <= 122);
            let diff = ch as int - 97;
            assert(0 <= diff <= 25);
            assert(upper_ascii == 65 + diff);
            assert(ch as int == 97 + diff);
            assert(upper_ascii == (97 + diff) - 32 == 65 + diff);
        };
        assert(is_lower_upper_pair(ch, upper_ascii as char));
        assert(shift_minus_32(ch) == upper_ascii as char);
    };
}

spec fn upper_map(i: int, c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32(c)
    } else {
        c
    }
}

exec fn is_lower_case_exec(c: char) -> (b: bool)
ensures
    b == is_lower_case(c)
{
    (c as u32 >= 97 && c as u32 <= 122)
}

exec fn shift_minus_32_exec(c: char) -> (res: char)
requires
    is_lower_case(c)
ensures
    res == shift_minus_32(c)
{
    let val = ((c as u32) - 32) % 128;
    proof {
        lemma_lower_shift();
        let upper = shift_minus_32(c);
        assert(65 <= upper as int <= 90);
        assert(val == upper as u32);
        // Therefore, char::from_u32(val) is Some
    };
    char::from_u32(val).unwrap()
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
    Seq::<char>::map(s, upper_map)
}
// </vc-code>

fn main() {
}

}