pub fn BinarySearch(arr: &[i32], target: i32) -> (index: i32)
    requires(distinct(arr))
    requires(sorted(arr))
    ensures(|index: i32| -1 <= index < arr.len() as i32)
    ensures(|index: i32| index == -1 ==> not_found(arr, target))
    ensures(|index: i32| index != -1 ==> found(arr, target, index))
{
}

pub open spec fn sorted(a: &[i32]) -> bool
{
   forall|j: usize, k: usize| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

pub open spec fn distinct(arr: &[i32]) -> bool
{
    forall|i: usize, j: usize| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

pub open spec fn not_found(arr: &[i32], target: i32) -> bool
{
    forall|j: usize| 0 <= j < arr.len() ==> arr[j] != target
}

pub open spec fn found(arr: &[i32], target: i32, index: i32) -> bool
    recommends(-1 <= index < arr.len() as i32)
{
    if index == -1 { false }
    else if arr[index as usize] == target { true }
    else { false }
}