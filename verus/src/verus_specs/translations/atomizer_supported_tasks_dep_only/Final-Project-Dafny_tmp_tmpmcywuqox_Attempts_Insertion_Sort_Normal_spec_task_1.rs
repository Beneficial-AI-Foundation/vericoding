pub fn lookForMin(a: &[i32], i: usize) -> (m: usize)
    requires(
        i < a.len()
    )
    ensures(|m: usize|
        i <= m && m < a.len() &&
        forall|k: usize| i <= k && k < a.len() ==> a[k as int] >= a[m as int]
    )
{
}