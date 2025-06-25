pub fn contains_z(s: &str) -> (result: bool)
    ensures(result <==> (exists|i: usize| 0 <= i < s.len() && (s[i] == 'z' || s[i] == 'Z')))
{
}