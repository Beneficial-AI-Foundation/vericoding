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
exec fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    97 <= c as u32 && c as u32 <= 122
}

exec fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    65 <= c as u32 && c as u32 <= 90
}

exec fn shift_minus_32_exec(c: char) -> (result: char)
    requires is_lower_case(c)
    ensures result == shift_minus_32(c)
{
    ((c as u32 - 32) as u8) as char
}

exec fn shift_32_exec(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == shift_32(c)
{
    ((c as u32 + 32) as u8) as char
}

proof fn lemma_lower_case_conversion(c: char)
    requires 97 <= c as int <= 122
    ensures is_lower_upper_pair(c, shift_minus_32(c))
{
    assert(97 <= c as int <= 122);
    assert(65 <= (c as int - 32) <= 90);
    assert((c as int) == (shift_minus_32(c) as int) + 32);
}

proof fn lemma_upper_case_conversion(c: char)
    requires 65 <= c as int <= 90
    ensures is_upper_lower_pair(c, shift_32(c))
{
    assert(65 <= c as int <= 90);
    assert(97 <= (c as int + 32) <= 122);
    assert((c as int) == (shift_32(c) as int) - 32);
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..s.len()
        invariant
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
    {
        let c = s[i];
        
        if is_lower_case_exec(c) {
            proof {
                lemma_lower_case_conversion(c);
            }
            result.push(shift_minus_32_exec(c));
        } else if is_upper_case_exec(c) {
            proof {
                lemma_upper_case_conversion(c);
            }
            result.push(shift_32_exec(c));
        } else {
            result.push(c);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}