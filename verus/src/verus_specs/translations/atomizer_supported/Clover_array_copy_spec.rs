pub fn iter_copy<T>(s: &[T]) -> (t: Vec<T>)
    ensures
        s.len() == t.len(),
        forall|i: usize| 0 <= i < s.len() ==> s[i] == t[i],
{
}