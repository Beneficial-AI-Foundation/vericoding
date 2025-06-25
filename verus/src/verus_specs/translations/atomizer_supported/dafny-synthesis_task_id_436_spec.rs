use vstd::prelude::*;

verus! {

spec fn is_negative(n: int) -> bool {
    n < 0
}

pub fn find_negative_numbers(arr: &[i32]) -> (negative_list: Vec<i32>)
    ensures
        // All numbers in the output are negative and exist in the input
        forall|i: int| 0 <= i < negative_list.len() ==> is_negative(negative_list[i] as int) && arr@.contains(negative_list[i]),
        // All negative numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i] as int) ==> negative_list@.contains(arr[i])
{
}

}