pub fn findMin(a: &mut [f64], from: usize, to: usize) -> usize
    requires
        0 <= from < to <= a.len(),
    ensures |index: usize|
        from <= index < to &&
        forall|k: usize| from <= k < to ==> a[k] >= a[index],
{
}