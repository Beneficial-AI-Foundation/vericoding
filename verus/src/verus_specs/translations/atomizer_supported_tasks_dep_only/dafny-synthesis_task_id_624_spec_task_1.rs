// ATOM 
pub open spec fn is_lower_case(c: char) -> bool
{
    97 <= c as int <= 122
}

// ATOM 
pub open spec fn is_lower_upper_pair(c: char, C: char) -> bool
{
    (c as int) == (C as int) + 32
}

// ATOM 
pub open spec fn shift_minus32(c: char) -> char
{
    ((c as int - 32) % 128) as char
}

// SPEC 
pub fn to_uppercase(s: &str) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) then is_lower_upper_pair(s[i], v[i]) else v[i] == s[i]
{
}