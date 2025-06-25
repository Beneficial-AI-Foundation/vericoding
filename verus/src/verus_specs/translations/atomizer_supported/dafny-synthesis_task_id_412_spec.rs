use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

pub fn remove_odd_numbers(arr: &[int]) -> (even_list: Vec<int>)
    ensures
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i]) && arr@.contains(even_list[i]),
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i]) ==> even_list@.contains(arr[i]),
{
}

}