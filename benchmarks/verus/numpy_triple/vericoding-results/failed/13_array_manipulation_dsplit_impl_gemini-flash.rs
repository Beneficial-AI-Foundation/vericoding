// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a function for safe integer division that proves the remainder is zero. */
fn safe_division_ensures_remainder_zero(numerator: int, denominator: int) -> int
    requires denominator != 0,
    ensures numerator % denominator == 0,
    ensures result == numerator / denominator
{
    numerator / denominator
}
// </vc-helpers>

// <vc-spec>
fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed arithmetic overflow/underflow in `original_arr_idx` calculation and added `get_proof` to satisfy `unwrap` precondition. */
{
    let sub_array_len: usize = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    proof {
        assert(sub_array_len == (arr.len() as int / sections as int)) by (nonlinear_arith);
    }
    while result.len() < sections
        invariant
            result.len() <= sections,
            result.len() as int >= 0,
            current_section_idx == result.len()@,
            sub_array_len == (arr.len() as int / sections as int),
            arr.len() as int >= 0,
            sections as int >= 0,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() as int == sub_array_len as int,
            forall|k: int, j: int| 0 <= k < result.len() && 0 <= j < sub_array_len as int ==> 
                result[k][j] == arr[k * sub_array_len as int + j],
        decreases sections - result.len()
    {
        let mut sub_vec: Vec<f32> = Vec::new();
        let current_section_idx = result.len();
        while sub_vec.len() < sub_array_len
            invariant
                current_section_idx as int >= 0,
                sub_vec.len() <= sub_array_len,
                sub_vec.len() as int >= 0,
                sub_array_len as int >= 0,
                arr.len() as int >= 0,
                ((current_section_idx as int * sub_array_len as int) + sub_vec.len() as int) <= arr.len() as int,
                forall|j: int| 0 <= j < sub_vec.len() ==> 
                    sub_vec[j] == arr[current_section_idx as int * sub_array_len as int + j],
            decreases sub_array_len - sub_vec.len()
        {
            let original_arr_idx: usize = (current_section_idx * sub_array_len) + sub_vec.len();
            proof {
                arr.get_proof(original_arr_idx);
            }
            sub_vec.push(*arr.get(original_arr_idx).unwrap());
        }
        result.push(sub_vec);
    }
    result
}
// </vc-code>

}
fn main() {}