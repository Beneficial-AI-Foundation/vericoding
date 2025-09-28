// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn string_is_decimal(s: &String) -> (b: bool)
    ensures
        b == (s@.len() > 0 && all_chars_decimal(s@)),
{
    if s.len() == 0 {
        assert(s@.len() == 0);
        return false;
    }

    if !s.is_ascii() {
        proof {
            if all_chars_decimal(s@) {
                lemma_all_chars_decimal_implies_ascii(s@);
                assert(s.is_ascii());
            }
        }
        return false;
    }

    lemma_all_chars_decimal_iff_all_bytes_decimal(s);
    
    let bytes = s.as_bytes();
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            s.is_ascii(),
            bytes@ == s.as_bytes()@,
            s.len() > 0,
            forall|j: int| 0 <= j < i ==> ('0' as u8 <= bytes@[j] && bytes@[j] <= '9' as u8),
    {
        let b = bytes[i];
        if !('0' as u8 <= b && b <= '9' as u8) {
            return false;
        }
        i = i + 1;
    }
    
    return true;
}

proof fn lemma_all_chars_decimal_implies_ascii(s_view: Seq<char>)
    requires
        all_chars_decimal(s_view),
    ensures
        forall|i: int| 0 <= i < s_view.len() ==> s_view[i].is_ascii(),
{
    assert forall|i: int| 0 <= i < s_view.len() implies s_view[i].is_ascii() by {
        let c = s_view[i];
        assert(is_decimal_char(c));
    };
}

proof fn lemma_all_chars_decimal_iff_all_bytes_decimal(s: &String)
    requires
        s.is_ascii(),
    ensures
        all_chars_decimal(s@) <==> (forall|i: int| 0 <= i < s.as_bytes().len() ==> '0' as u8 <= s.as_bytes()@[i] && s.as_bytes()@[i] <= '9' as u8),
{
    vstd::string::lemma_ascii_len_eq_bytes_len(s);
    vstd::string::lemma_string_is_ascii_means_view_is_ascii(s);
    vstd::bytes::lemma_ascii_chars_as_bytes(s@);
    assert(s.as_bytes()@ == s@.map(|c: char| c as u8));
    assert forall|i: int| 0 <= i < s@.len() implies is_decimal_char(s@[i]) <==> ('0' as u8 <= s.as_bytes()@[i] && s.as_bytes()@[i] <= '9' as u8) by {
        let c = s@[i];
        let b = s.as_bytes()@[i];
        assert(c.is_ascii());
        assert(b == c as u8);
    };
}
// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result[j] == (a[j]@.len() > 0 && all_chars_decimal(a[j]@))),
    {
        let is_dec = string_is_decimal(&a[i]);
        result.push(is_dec);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}