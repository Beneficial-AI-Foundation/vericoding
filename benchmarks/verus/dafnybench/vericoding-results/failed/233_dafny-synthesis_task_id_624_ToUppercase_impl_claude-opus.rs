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
spec fn convert_char(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32(c)
    } else {
        c
    }
}

proof fn lemma_shift_creates_pair(c: char)
    requires is_lower_case(c)
    ensures is_lower_upper_pair(c, shift_minus_32(c))
{
    assert((c as int - 32) % 128 == c as int - 32) by {
        assert(97 <= c as int <= 122);
        assert(65 <= c as int - 32 <= 90);
        assert(0 <= c as int - 32 < 128);
    }
    assert(shift_minus_32(c) as int == c as int - 32);
    assert(c as int == shift_minus_32(c) as int + 32);
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
    let mut result = Seq::<char>::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                if is_lower_case(#[trigger] s@[j]) {
                    is_lower_upper_pair(s@[j], result@[j])
                } else {
                    result@[j] == s@[j]
                }
    {
        let c = s@[i];
        let new_c = if 97 <= (c as u8) && (c as u8) <= 122 {
            proof {
                assert(is_lower_case(c));
                lemma_shift_creates_pair(c);
            }
            (((c as u8) - 32) as char)
        } else {
            c
        };
        
        proof {
            if is_lower_case(c) {
                assert(97 <= c as int <= 122);
                assert(65 <= c as int - 32 <= 90);
                assert((c as int - 32) % 128 == c as int - 32);
                assert(new_c as int == c as int - 32);
                assert(is_lower_upper_pair(c, new_c));
            }
        }
        
        result = result.push(new_c);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}