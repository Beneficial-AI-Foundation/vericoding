pub fn binarySearch(a: &[i32], val: i32) -> (pos: i32)
    requires
        a.len() > 0,
        forall|i: usize, j: usize| 0 <= i < j < a.len() ==> a[i] <= a[j],
    ensures
        |pos: i32| 0 <= pos < a.len() ==> a[pos as usize] == val,
        |pos: i32| pos < 0 || pos >= a.len() ==> forall|i: usize| 0 <= i < a.len() ==> a[i] != val,
{
}