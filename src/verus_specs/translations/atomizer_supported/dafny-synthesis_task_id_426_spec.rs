spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

pub fn filter_odd_numbers(arr: &[i32]) -> Vec<i32>
    ensures(forall|i: int| 0 <= i < result.len() ==> is_odd(result[i] as int) && arr@.contains(result[i]))
    ensures(forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> result@.contains(arr[i]))
{
}