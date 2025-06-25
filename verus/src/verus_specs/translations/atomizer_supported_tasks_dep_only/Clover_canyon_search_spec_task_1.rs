pub fn canyon_search(a: &[i32], b: &[i32]) -> usize
    requires(
        a.len() != 0 && b.len() != 0
    )
    requires(
        forall|i: usize, j: usize| 0 <= i < j < a.len() ==> a[i] <= a[j]
    )
    requires(
        forall|i: usize, j: usize| 0 <= i < j < b.len() ==> b[i] <= b[j]
    )
    ensures(|d: usize|
        exists|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < b.len() && d == if a[i] < b[j] { (b[j] - a[i]) as usize } else { (a[i] - b[j]) as usize }
    )
    ensures(|d: usize|
        forall|i: usize, j: usize| 0 <= i < a.len() && 0 <= j < b.len() ==> d <= if a[i] < b[j] { (b[j] - a[i]) as usize } else { (a[i] - b[j]) as usize }
    )
{
}