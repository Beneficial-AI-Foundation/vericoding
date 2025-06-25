// ATOM
pub open spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

// SPEC
pub fn count_vowel_neighbors(s: &str) -> (count: i32)
    requires(
        s.len() <= i32::MAX
    )
    ensures(
        count >= 0 &&
        count == (set_int_range(1, s.len() as int - 1).filter(
            |i: int| 1 <= i < s.len() - 1 && 
                    is_vowel(s@[i-1]) && 
                    is_vowel(s@[i+1])
        ).len() as i32)
    )
{
}