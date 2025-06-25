pub fn ArrayToSeq(a: &[i32]) -> (s: Vec<i32>)
    requires(true)
    ensures(|s| == a.len())
    ensures(forall|i: usize| 0 <= i < a.len() ==> s[i] == a[i])
{
}