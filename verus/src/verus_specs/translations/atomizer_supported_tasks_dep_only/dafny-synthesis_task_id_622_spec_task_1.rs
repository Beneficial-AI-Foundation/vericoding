pub fn find_median(a: &[i32], b: &[i32]) -> i32
    requires(
        a.len() == b.len() &&
        a.len() > 0 &&
        (forall|i: usize| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1]) &&
        (forall|i: usize| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1])
    )
    ensures(|median: i32|
        median == if a.len() % 2 == 0 { (a[a.len() / 2 - 1] + b[0]) / 2 } else { a[a.len() / 2] }
    )
{
}