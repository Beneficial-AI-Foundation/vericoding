// ATOM 
spec fn insertion_sorted(array: &[i32], left: int, right: int) -> bool
{
    0 <= left <= right <= array.len() &&
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// SPEC
pub fn sorting(array: &mut [i32])
    requires 
        array.len() > 1,
    ensures
        insertion_sorted(array, 0, array.len() as int),
{
}