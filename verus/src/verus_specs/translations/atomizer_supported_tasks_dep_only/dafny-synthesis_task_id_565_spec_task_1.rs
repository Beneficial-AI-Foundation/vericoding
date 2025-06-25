pub fn split_string_into_chars(s: &str) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: usize| 0 <= i < s.len() ==> v[i] == s.chars().nth(i).unwrap(),
{
}