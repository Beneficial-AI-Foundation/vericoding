pub fn maxArrayReverse(arr: &[i32]) -> (max: i32)
    requires(arr.len() > 0)
    ensures(|max: i32| forall|i: usize| 0 <= i < arr.len() ==> arr[i] <= max)
    ensures(|max: i32| exists|x: usize| 0 <= x < arr.len() && arr[x] == max)
{
}