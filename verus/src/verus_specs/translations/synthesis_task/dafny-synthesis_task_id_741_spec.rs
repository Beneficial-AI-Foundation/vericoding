pub fn AllCharactersSame(s: &str) -> (result: bool)
    ensures(result ==> forall|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j])
    ensures(!result ==> (s.len() > 1) && (exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j]))
{
}