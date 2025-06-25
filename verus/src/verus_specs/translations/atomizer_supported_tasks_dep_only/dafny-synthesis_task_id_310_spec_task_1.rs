pub fn to_char_array(s: &str) -> Vec<char>
    ensures(|result: Vec<char>| result.len() == s.len())
    ensures(|result: Vec<char>| forall|i: usize| 0 <= i < s.len() ==> result[i] == s.chars().nth(i).unwrap())
{
}