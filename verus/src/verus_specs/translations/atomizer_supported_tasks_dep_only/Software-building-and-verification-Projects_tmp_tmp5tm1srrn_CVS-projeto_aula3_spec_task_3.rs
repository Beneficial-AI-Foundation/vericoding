pub fn maxArray(arr: &[int]) -> (max: int)
    requires(arr.len() > 0)
    ensures(forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max)
    ensures(exists|x: int| 0 <= x < arr.len() && arr[x] == max)
{
}

pub fn maxArray(arr: &[int]) -> (max: int)
    requires(arr.len() > 0)
    ensures(forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max)
    ensures(exists|x: int| 0 <= x < arr.len() && arr[x] == max)
{
}