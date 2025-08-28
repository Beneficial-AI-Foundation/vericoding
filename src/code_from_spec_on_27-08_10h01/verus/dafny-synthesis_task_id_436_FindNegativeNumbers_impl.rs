use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
spec fn contains_element(v: Vec<int>, elem: int) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == elem
}

spec fn all_elements_negative(v: Vec<int>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> is_negative(v[i])
}

spec fn all_elements_from_source(v: Vec<int>, source: &[int]) -> bool {
    forall|i: int| 0 <= i < v.len() ==> 
        exists|j: int| 0 <= j < source.len() && source[j] == v[i]
}

spec fn contains_all_negatives_from_source(v: Vec<int>, source: &[int]) -> bool {
    forall|i: int| 0 <= i < source.len() && is_negative(source[i]) ==> 
        contains_element(v, source[i])
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut negative_list = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            all_elements_negative(negative_list),
            all_elements_from_source(negative_list, arr),
            forall|k: int| 0 <= k < i && is_negative(arr[k]) ==> 
                contains_element(negative_list, arr[k]),
    {
        if arr[i as int] < 0int {
            negative_list.push(arr[i as int]);
        }
        i += 1;
    }
    
    negative_list
}
// </vc-code>

fn main() {}

}