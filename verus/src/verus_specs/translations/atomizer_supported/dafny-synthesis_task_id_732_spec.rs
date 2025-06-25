// ATOM 
pub open spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}

// SPEC 

pub fn replace_with_colon(s: &str) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (is_space_comma_dot(s[i as usize]) ==> v[i as usize] == ':') && (!is_space_comma_dot(s[i as usize]) ==> v[i as usize] == s[i as usize])
{
}