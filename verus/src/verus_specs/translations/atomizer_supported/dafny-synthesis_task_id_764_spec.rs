// ATOM 
pub open spec fn is_digit(c: char) -> bool
{
    48 <= c as int <= 57
}

// SPEC 
pub fn count_digits(s: &str) -> (count: i32)
    ensures
        count >= 0,
        count == (set_int_range(0, s.len() as int).filter(|i: int| is_digit(s.index(*i)))).len(),
{
}