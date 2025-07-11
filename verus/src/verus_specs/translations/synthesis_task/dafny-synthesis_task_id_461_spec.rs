// ATOM
pub closed spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// SPEC
pub fn count_uppercase(s: &str) -> (count: i32)
    ensures
        count >= 0,
        count == (set_int_range(0, s.len() as int).filter(|i: int| is_upper_case(s[*i as usize]))).len() as i32,
{
}