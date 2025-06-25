pub fn replace_chars(s: &str, old_char: char, new_char: char) -> (v: String)
    requires(
        s.is_ascii()
    )
    ensures(|v: String|
        v.len() == s.len() &&
        forall|i: int| 0 <= i < s.len() ==> 
            (s[i] == old_char ==> v[i] == new_char) && 
            (s[i] != old_char ==> v[i] == s[i])
    )
{
    unimplemented!()
}