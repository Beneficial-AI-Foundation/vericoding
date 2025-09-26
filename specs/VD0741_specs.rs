// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}