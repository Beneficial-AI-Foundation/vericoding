pub fn find_first_repeated_char(s: &str) -> (found: bool, c: char)
    ensures(found ==> exists|i: int, j: int| 0 <= i < j < s.len() && s[i] == s[j] && s[i] == c && (forall|k: int, l: int| 0 <= k < l < j && s[k] == s[l] ==> k >= i))
    ensures(!found ==> (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]))
{
}