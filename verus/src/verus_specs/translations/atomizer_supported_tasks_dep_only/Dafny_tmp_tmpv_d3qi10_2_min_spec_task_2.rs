pub fn minArray(a: &[i32]) -> (m: i32)
    requires(a.len() > 0)
    ensures(|m: i32| forall|k: usize| 0 <= k < a.len() ==> m <= a[k])
    ensures(|m: i32| exists|k: usize| 0 <= k < a.len() && m == a[k])
{
}