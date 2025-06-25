use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

pub fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)
    ensures 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == odd_list[i],
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> exists|j: int| 0 <= j < odd_list.len() && odd_list[j] == arr[i]
{
}

}