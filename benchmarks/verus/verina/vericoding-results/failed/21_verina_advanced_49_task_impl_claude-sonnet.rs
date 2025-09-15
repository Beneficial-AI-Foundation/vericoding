// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches by converting usize to int */
proof fn merge_maintains_order(result: &Vec<i32>, new_elem: i32, old_len: usize)
    requires
        old_len == result.len(),
        old_len == 0 || result[old_len as int - 1] <= new_elem,
        forall|i: int, j: int| 0 <= i < j < old_len as int ==> result[i] <= result[j]
    ensures
        forall|i: int, j: int| 0 <= i < j < old_len as int + 1 ==> (if j == old_len as int + 1 { result[i] <= new_elem } else { result[i] <= result[j] })
{
}

proof fn sortedness_extends(arr: &Vec<i32>, result: &Vec<i32>, arr_idx: usize, result_len: usize)
    requires
        arr_idx < arr.len(),
        result_len == result.len(),
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        forall|i: int, j: int| 0 <= i < j < result_len as int ==> result[i] <= result[j],
        result_len == 0 || result[result_len as int - 1] <= arr[arr_idx as int]
    ensures
        forall|i: int, j: int| 0 <= i < j < result_len as int + 1 ==> (if j == result_len as int + 1 { result[i] <= arr[arr_idx as int] } else { result[i] <= result[j] })
{
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by converting usize to int */
    let mut result: Vec<i32> = Vec::new();
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    while i1 < arr1.len() && i2 < arr2.len()
        invariant
            i1 <= arr1.len(),
            i2 <= arr2.len(),
            result.len() == i1 + i2,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
            forall|k: int| 0 <= k < i1 as int ==> (result.len() == 0 || result[result.len() as int - 1] >= arr1[k]),
            forall|k: int| 0 <= k < i2 as int ==> (result.len() == 0 || result[result.len() as int - 1] >= arr2[k])
        decreases arr1.len() - i1 + arr2.len() - i2
    {
        if arr1[i1 as int] <= arr2[i2 as int] {
            proof {
                if result.len() > 0 {
                    assert(forall|k: int| 0 <= k < i2 as int ==> result[result.len() as int - 1] >= arr2[k]);
                    assert(arr1[i1 as int] <= arr2[i2 as int]);
                }
            }
            result.push(arr1[i1 as int]);
            i1 += 1;
        } else {
            proof {
                if result.len() > 0 {
                    assert(forall|k: int| 0 <= k < i1 as int ==> result[result.len() as int - 1] >= arr1[k]);
                    assert(arr2[i2 as int] < arr1[i1 as int]);
                }
            }
            result.push(arr2[i2 as int]);
            i2 += 1;
        }
    }
    
    while i1 < arr1.len()
        invariant
            i1 <= arr1.len(),
            i2 == arr2.len(),
            result.len() == i1 + i2,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
            result.len() == 0 || forall|k: int| i1 as int <= k < arr1.len() ==> result[result.len() as int - 1] <= arr1[k]
        decreases arr1.len() - i1
    {
        proof {
            if result.len() > 0 && i1 < arr1.len() {
                if i1 > 0 {
                    assert(arr1[i1 as int - 1] <= arr1[i1 as int]);
                }
            }
        }
        result.push(arr1[i1 as int]);
        i1 += 1;
    }
    
    while i2 < arr2.len()
        invariant
            i1 == arr1.len(),
            i2 <= arr2.len(),
            result.len() == i1 + i2,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
            result.len() == 0 || forall|k: int| i2 as int <= k < arr2.len() ==> result[result.len() as int - 1] <= arr2[k]
        decreases arr2.len() - i2
    {
        proof {
            if result.len() > 0 && i2 < arr2.len() {
                if i2 > 0 {
                    assert(arr2[i2 as int - 1] <= arr2[i2 as int]);
                }
            }
        }
        result.push(arr2[i2 as int]);
        i2 += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}