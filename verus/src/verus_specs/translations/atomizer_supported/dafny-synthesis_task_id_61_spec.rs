// ATOM
pub open spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// SPEC
pub fn count_substrings_with_sum_of_digits_equal_to_length(s: &str) -> (count: i32)
    ensures count >= 0
{
}