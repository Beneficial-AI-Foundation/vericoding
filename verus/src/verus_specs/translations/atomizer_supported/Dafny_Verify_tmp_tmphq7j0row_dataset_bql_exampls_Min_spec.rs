pub fn min(a: &[i32], n: usize) -> (min: i32)
    requires(
        0 < n <= a.len()
    )
    ensures(|min: i32|
        exists|i: usize| 0 <= i && i < n && a[i as int] == min
    )
    ensures(|min: i32|
        forall|i: usize| 0 <= i && i < n ==> a[i as int] >= min
    )
{
}