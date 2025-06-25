pub fn remove_chars(s1: &str, s2: &str) -> (v: String)
    requires(
        true
    )
    ensures(|v: String|
        v.len() <= s1.len() &&
        forall|i: usize| 0 <= i < v.len() ==> s1.contains(v.chars().nth(i).unwrap()) && !s2.contains(v.chars().nth(i).unwrap()) &&
        forall|i: usize| 0 <= i < s1.len() ==> s2.contains(s1.chars().nth(i).unwrap()) || v.contains(s1.chars().nth(i).unwrap())
    )
{
}