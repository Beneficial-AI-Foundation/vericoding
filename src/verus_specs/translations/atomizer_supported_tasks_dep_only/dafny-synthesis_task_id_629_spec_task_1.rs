// ATOM 
spec fn is_even(n: int) -> bool
{
    n % 2 == 0
}

// SPEC 

pub fn find_even_numbers(arr: &[int]) -> Vec<int>
    ensures(forall|i: int| 0 <= i < result.len() ==> is_even(result[i]) && arr@.contains(result[i]))
    ensures(forall|i: int| 0 <= i < arr.len() && is_even(arr[i]) ==> result@.contains(arr[i]))
{
}