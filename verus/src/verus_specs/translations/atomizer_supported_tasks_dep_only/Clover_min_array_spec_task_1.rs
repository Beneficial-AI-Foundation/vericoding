pub fn minArray(a: &[i32]) -> (r: i32)
    requires(a.len() > 0)
    ensures(forall|i: usize| 0 <= i < a.len() ==> r <= a[i])
    ensures(exists|i: usize| 0 <= i < a.len() && r == a[i])
{
}