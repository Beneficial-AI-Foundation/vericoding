pub fn minimum(a: &[i32]) -> (m: i32)
    requires(a.len() > 0)
    ensures(exists|i: usize| 0 <= i < a.len() && m == a[i])
    ensures(forall|i: usize| 0 <= i < a.len() ==> m <= a[i])
{
}