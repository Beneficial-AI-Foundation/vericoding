pub fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

pub fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

pub fn shift_minus_32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

pub fn to_uppercase(s: &str) -> (v: String)
    ensures(
        v.len() == s.len()
    )
    ensures(
        forall|i: usize| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) { 
                is_lower_upper_pair(s[i], v[i]) 
            } else { 
                v[i] == s[i] 
            }
    )
{
}