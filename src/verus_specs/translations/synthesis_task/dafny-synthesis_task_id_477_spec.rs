// ATOM
pub open spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// ATOM
pub open spec fn is_upper_lower_pair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

// ATOM
pub open spec fn shift32(c: char) -> char {
    ((c as int + 32) % 128) as char
}

// SPEC
pub fn to_lowercase(s: &str) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_upper_case(s[i]) { 
                is_upper_lower_pair(s[i], v[i]) 
            } else { 
                v[i] == s[i] 
            }
{
}