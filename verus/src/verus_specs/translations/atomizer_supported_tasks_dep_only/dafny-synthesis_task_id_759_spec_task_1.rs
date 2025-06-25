pub fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures(result ==> (exists|i: usize| 0 <= i < s.len() && s.as_bytes()[i] == b'.' && s.len() - i - 1 == 2))
    ensures(!result ==> !(exists|i: usize| 0 <= i < s.len() && s.as_bytes()[i] == b'.' && s.len() - i - 1 == 2))
{
}