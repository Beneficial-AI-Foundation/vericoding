use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
spec fn negatives_from_prefix(arr: Seq<int>, end: int) -> Seq<int>
    decreases end,
{
    if end == 0 {
        Seq::empty()
    } else {
        let rest = negatives_from_prefix(arr, end - 1);
        if arr[end - 1] < 0 {
            rest.push(arr[end - 1])
        } else {
            rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures
        // All numbers in the output are negative and exist in the input
        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],
        // All negative numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == negatives_from_prefix(arr@, i as int),
    {
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}

}