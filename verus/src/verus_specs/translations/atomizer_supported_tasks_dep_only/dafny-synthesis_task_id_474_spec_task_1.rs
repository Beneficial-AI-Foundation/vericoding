pub fn replace_chars(s: &str, old_char: char, new_char: char) -> (v: String)
    requires(s.len() <= usize::MAX)
    ensures(|v: String| v.len() == s.len())
    ensures(|v: String| forall|i: usize| 0 <= i < s.len() ==> 
        (s.get_char(i) == old_char ==> v.get_char(i) == new_char) && 
        (s.get_char(i) != old_char ==> v.get_char(i) == s.get_char(i)))
{
}