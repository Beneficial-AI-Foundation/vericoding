spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

pub fn CountDigits(s: &str) -> (count: i32)
    ensures
        count >= 0,
        count == (set_int_range(0, s.len() as int).filter(|i: int| IsDigit(s[*i as usize]))).len(),
{
}