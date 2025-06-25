// ATOM
pub open spec fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

// ATOM
pub open spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// ATOM
pub open spec fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

// ATOM
pub open spec fn is_upper_lower_pair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

// ATOM
pub open spec fn shift_minus32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

// ATOM
pub open spec fn shift32(c: char) -> char {
    ((c as int + 32) % 128) as char
}

// SPEC
pub fn toggle_case(s: &str) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i as usize]) {
                is_lower_upper_pair(s[i as usize], v[i as usize])
            } else if is_upper_case(s[i as usize]) {
                is_upper_lower_pair(s[i as usize], v[i as usize])
            } else {
                v[i as usize] == s[i as usize]
            }
{
}