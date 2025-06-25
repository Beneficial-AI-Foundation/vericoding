// ATOM
pub open spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

// SPEC
pub fn count_vowel_neighbors(s: &str) -> (count: usize)
    ensures(count >= 0)
    ensures(count == Set::new(|i: int| 1 <= i < s.len() - 1 && is_vowel(s[i-1]) && is_vowel(s[i+1])).len())
{
}