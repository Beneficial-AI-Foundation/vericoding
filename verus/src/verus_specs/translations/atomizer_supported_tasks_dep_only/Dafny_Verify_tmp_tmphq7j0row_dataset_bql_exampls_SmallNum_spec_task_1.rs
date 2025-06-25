pub fn add_small_numbers(a: &[int], n: int, max: int) -> (r: int)
    requires(n > 0)
    requires(n <= a.len())
    requires(forall|i: int| 0 <= i && i < n ==> a[i] <= max)
    ensures(|r: int| r <= max * n)
{
}