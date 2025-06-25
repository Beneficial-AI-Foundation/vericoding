pub fn all_characters_same(s: &str) -> (result: bool)
    ensures(result ==> forall|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() ==> s.as_bytes()[i] == s.as_bytes()[j])
    ensures(!result ==> (s.len() > 1) && (exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.as_bytes()[i] != s.as_bytes()[j]))
{
}