pub fn replace_blanks_with_char(s: &str, ch: char) -> (v: String)
    ensures(
        v.len() == s.len() &&
        forall|i: usize| 0 <= i < s.len() ==> 
            (s.as_bytes()[i] == b' ' ==> v.as_bytes()[i] == ch as u8) &&
            (s.as_bytes()[i] != b' ' ==> v.as_bytes()[i] == s.as_bytes()[i])
    )
{
}