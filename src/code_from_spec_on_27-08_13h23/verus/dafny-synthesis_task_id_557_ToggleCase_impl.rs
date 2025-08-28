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
proof fn lemma_shift_minus_32_lower_to_upper(c: char)
    requires
        is_lower_case(c),
    ensures
        is_lower_upper_pair(c, shift_minus_32(c)),
        is_upper_case(shift_minus_32(c)),
{
    assert(is_lower_case(c));
    assert(97 <= c as int <= 122);
    assert(c as int - 32 >= 65 && c as int - 32 <= 90);
    assert(is_upper_case(shift_minus_32(c)));
    assert((c as int) == (shift_minus_32(c) as int) + 32);
}

proof fn lemma_shift_32_upper_to_lower(c: char)
    requires
        is_upper_case(c),
    ensures
        is_upper_lower_pair(c, shift_32(c)),
        is_lower_case(shift_32(c)),
{
    assert(is_upper_case(c));
    assert(65 <= c as int <= 90);
    assert(c as int + 32 >= 97 && c as int + 32 <= 122);
    assert(is_lower_case(shift_32(c)));
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
{
    let mut result: Vec<char> = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let s_char = #[trigger] s[j];
                let v_char = result[j];
                if is_lower_case(s_char) {
                    is_lower_upper_pair(s_char, v_char)
                } else if is_upper_case(s_char) {
                    is_upper_lower_pair(s_char, v_char)
                } else {
                    v_char == s_char
                }
            }
    {
        let c = s[i];
        if is_lower_case(c) {
            lemma_shift_minus_32_lower_to_upper(c);
            result.push(shift_minus_32(c));
        } else if is_upper_case(c) {
            lemma_shift_32_upper_to_lower(c);
            result.push(shift_32(c));
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