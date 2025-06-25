pub fn find_first_repeated_char(s: &str) -> (found: bool, c: char)
    ensures(found ==> exists|i: usize, j: usize| 0 <= i < j < s.len() && s[i] == s[j] && s[i] == c && (forall|k: usize, l: usize| 0 <= k < l < j && s[k] == s[l] ==> k >= i))
    ensures(!found ==> (forall|i: usize, j: usize| 0 <= i < j < s.len() ==> s[i] != s[j]))
{
}