pub fn iter_copy<T>(s: &[T]) -> (t: Vec<T>)
    requires(true)
    ensures(|t: Vec<T>| s.len() == t.len())
    ensures(|t: Vec<T>| forall|i: usize| 0 <= i < s.len() ==> s[i] == t[i])
{
}