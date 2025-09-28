use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

spec fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

spec fn is_upper_lower_pair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn shift_minus_32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

spec fn shift_32(c: char) -> char {
    ((c as int + 32) % 128) as char
}

// <vc-helpers>
proof fn lemma_lower_to_upper_conversion(c: char)
    requires is_lower_case(c)
    ensures 
        is_upper_case(shift_minus_32(c)),
        is_lower_upper_pair(c, shift_minus_32(c))
{
    assert(97 <= c as int <= 122);
    assert(65 <= (c as int - 32) <= 90);
    assert((c as int - 32) % 128 == c as int - 32);
}

proof fn lemma_upper_to_lower_conversion(c: char)
    requires is_upper_case(c)
    ensures 
        is_lower_case(shift_32(c)),
        is_upper_lower_pair(c, shift_32(c))
{
    assert(65 <= c as int <= 90);
    assert(97 <= (c as int + 32) <= 122);
    assert((c as int + 32) % 128 == c as int + 32);
}

fn exec_shift_minus_32(c: char) -> (result: char)
    requires is_lower_case(c)
    ensures result == shift_minus_32(c)
{
    assert(97 <= c as int <= 122);
    assert(65 <= (c as int - 32) <= 90);
    assert((c as int - 32) % 128 == c as int - 32);
    ((c as u8 - 32) as char)
}

fn exec_shift_32(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == shift_32(c)
{
    assert(65 <= c as int <= 90);
    assert(97 <= (c as int + 32) <= 122);
    assert((c as int + 32) % 128 == c as int + 32);
    ((c as u8 + 32) as char)
}
// </vc-helpers>

// <vc-spec>
fn toggle_case(s: Vec<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            let s_char = #[trigger] s[i];
            let v_char = v[i];
            if is_lower_case(s_char) {
                is_lower_upper_pair(s_char, v_char)
            } else if is_upper_case(s_char) {
                is_upper_lower_pair(s_char, v_char)
            } else {
                v_char == s_char
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let s_char = #[trigger] s[j];
                let r_char = result[j];
                if is_lower_case(s_char) {
                    is_lower_upper_pair(s_char, r_char)
                } else if is_upper_case(s_char) {
                    is_upper_lower_pair(s_char, r_char)
                } else {
                    r_char == s_char
                }
            }
        decreases s.len() - i
    {
        let c = s[i];
        
        if c >= 'a' && c <= 'z' {
            assert(is_lower_case(c));
            let new_c = exec_shift_minus_32(c);
            proof { lemma_lower_to_upper_conversion(c); }
            result.push(new_c);
        } else if c >= 'A' && c <= 'Z' {
            assert(is_upper_case(c));
            let new_c = exec_shift_32(c);
            proof { lemma_upper_to_lower_conversion(c); }
            result.push(new_c);
        } else {
            result.push(c);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}