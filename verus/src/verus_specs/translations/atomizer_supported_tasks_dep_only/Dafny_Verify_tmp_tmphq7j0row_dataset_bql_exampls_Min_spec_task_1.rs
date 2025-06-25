pub fn min(a: &[i32], n: i32) -> (min: i32)
    requires(0 < n <= a.len())
    ensures(exists|i: i32| 0 <= i && i < n && a[i as usize] == min)
    ensures(forall|i: i32| 0 <= i && i < n ==> a[i as usize] >= min)
{
}