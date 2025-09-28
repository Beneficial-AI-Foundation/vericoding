// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool
{
    'a' <= c && c <= 'z'
}

spec fn shift_minus_32(c: char) -> char
{
    arbitrary()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provided convert_char helper */
fn convert_char(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        (c as u8 - 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            let c = #[trigger] s@.index(i);
            let r = result@.index(i);
            if is_lower_case(c) {
                r == shift_minus_32(c)
            } else {
                r == c
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced String::push with Vec<char> and collect */
    let mut chars: Vec<char> = Vec::new();
    let mut index = 0;
    let mut iter = s.chars();
    loop
        invariant
            chars.len() == index,
            forall|j: int| 0 <= j < index ==> {
                let c_orig = #[trigger] s@.index(j);
                let r = chars[j as usize];
                if is_lower_case(c_orig) {
                    r == shift_minus_32(c_orig)
                } else {
                    r == c_orig
                }
            },
            index <= s@.len()
        decreases s@.len() - index
    {
        match iter.next() {
            Some(c) => {
                let converted = convert_char(c);
                chars.push(converted);
                index += 1;
            },
            None => break,
        }
    }
    let result = chars.into_iter().collect::<String>();
    result
}
// </vc-code>

}
fn main() {}