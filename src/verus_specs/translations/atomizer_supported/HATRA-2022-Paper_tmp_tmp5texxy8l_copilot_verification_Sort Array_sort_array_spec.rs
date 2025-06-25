pub fn sortArray(arr: &mut Vec<i32>) -> Vec<i32>
    requires(
        0 <= arr.len() < 10000
    )
    ensures(|arr_sorted: Vec<i32>|
        sorted(&arr_sorted, 0, arr_sorted.len()) &&
        multiset(arr@) == multiset(arr_sorted@)
    )
{
    unimplemented!()
}

spec fn sorted(arr: &Vec<i32>, start: int, end: int) -> bool
    recommends(
        0 <= start <= end <= arr.len()
    )
{
    forall|i: int, j: int| start <= i <= j < end ==> arr[i] <= arr[j]
}

spec fn pivot(arr: &Vec<i32>, pivot: int) -> bool
    recommends(
        0 <= pivot <= arr.len()
    )
{
    forall|u: int, v: int| 0 <= u < pivot < v < arr.len() ==> arr[u] <= arr[v]
}