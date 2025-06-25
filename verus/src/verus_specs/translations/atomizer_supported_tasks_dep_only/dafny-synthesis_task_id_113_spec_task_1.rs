// ATOM 
pub open spec fn is_digit(c: char) -> bool
{
    48 <= c as int <= 57
}

// SPEC 

pub fn is_integer(s: &str) -> (result: bool)
    ensures
        result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i as usize]))
{
}