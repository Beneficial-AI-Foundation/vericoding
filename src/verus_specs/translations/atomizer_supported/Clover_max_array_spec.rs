pub fn maxArray(a: &[i32]) -> (m: i32)
    requires(a.len() >= 1)
    ensures(forall|k: usize| 0 <= k && k < a.len() ==> m >= a[k])
    ensures(exists|k: usize| 0 <= k && k < a.len() && m == a[k])
{
}