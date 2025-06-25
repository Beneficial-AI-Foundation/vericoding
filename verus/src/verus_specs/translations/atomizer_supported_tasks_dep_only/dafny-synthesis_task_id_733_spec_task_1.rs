pub fn find_first_occurrence(arr: &[i32], target: i32) -> (index: i32)
    requires forall|i: usize, j: usize| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.len() ==> arr[index] == target
    ensures index == -1 ==> forall|i: usize| 0 <= i < arr.len() ==> arr[i] != target
    ensures forall|i: usize| 0 <= i < arr.len() ==> arr[i] == old(arr)[i]
{
}