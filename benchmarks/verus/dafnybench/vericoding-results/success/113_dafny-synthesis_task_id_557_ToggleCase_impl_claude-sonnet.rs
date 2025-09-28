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
fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    97 <= c as u32 && c as u32 <= 122
}

fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    65 <= c as u32 && c as u32 <= 90
}

fn to_upper_case_exec(c: char) -> (result: char)
    requires is_lower_case(c)
    ensures result == to_upper_case(c)
{
    ((c as u32 - 32) as u8) as char
}

fn to_lower_case_exec(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == to_lower_case(c)
{
    ((c as u32 + 32) as u8) as char
}

spec fn to_upper_case(c: char) -> char
    recommends is_lower_case(c)
{
    shift_minus_32(c)
}

spec fn to_lower_case(c: char) -> char
    recommends is_upper_case(c)
{
    shift_32(c)
}

proof fn lemma_lower_to_upper_conversion(c: char)
    requires is_lower_case(c)
    ensures 
        is_upper_case(to_upper_case(c)),
        is_lower_upper_pair(c, to_upper_case(c))
{
    let upper_c = to_upper_case(c);
    assert(upper_c as int == (c as int - 32) % 128);
    assert(97 <= c as int <= 122);
    assert(65 <= c as int - 32 <= 90);
    assert(upper_c as int == c as int - 32);
    assert(is_upper_case(upper_c));
    assert(c as int == upper_c as int + 32);
    assert(is_lower_upper_pair(c, upper_c));
}

proof fn lemma_upper_to_lower_conversion(c: char)
    requires is_upper_case(c)
    ensures 
        is_lower_case(to_lower_case(c)),
        is_upper_lower_pair(c, to_lower_case(c))
{
    let lower_c = to_lower_case(c);
    assert(lower_c as int == (c as int + 32) % 128);
    assert(65 <= c as int <= 90);
    assert(97 <= c as int + 32 <= 122);
    assert(lower_c as int == c as int + 32);
    assert(is_lower_case(lower_c));
    assert(c as int == lower_c as int - 32);
    assert(is_upper_lower_pair(c, lower_c));
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
        let new_char = if is_lower_case_exec(c) {
            proof { lemma_lower_to_upper_conversion(c); }
            to_upper_case_exec(c)
        } else if is_upper_case_exec(c) {
            proof { lemma_upper_to_lower_conversion(c); }
            to_lower_case_exec(c)
        } else {
            c
        };
        
        result.push(new_char);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}