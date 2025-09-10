use vstd::prelude::*;

verus! {

spec fn is_negative(n: int) -> bool {
    n < 0
}

fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures

        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],

        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
{
    assume(false);
    unreached()
}

}
fn main() {}