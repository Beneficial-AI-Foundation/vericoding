pub fn string_swap(s: &str, i: usize, j: usize) -> (t: String)
    requires(
        i >= 0 && j >= 0 && s.len() >= 0
    )
    requires(
        s.len() > 0 ==> i < s.len() && j < s.len()
    )
    ensures(|t: String|
        multiset(s@) == multiset(t@) &&
        s.len() == t.len() &&
        (s.len() > 0 ==> forall|k: usize| k != i && k != j && k < s.len() ==> t[k] == s[k]) &&
        (s.len() > 0 ==> t[i] == s[j] && t[j] == s[i]) &&
        (s.len() == 0 ==> t@ == s@)
    )
{
    unimplemented!()
}

pub fn check() {
}