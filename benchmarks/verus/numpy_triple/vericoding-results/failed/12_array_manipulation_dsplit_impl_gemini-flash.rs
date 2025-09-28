// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helper */
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
/* code modified by LLM (iteration 5): Fixed array indexing and added asserts. */
{
    let section_len = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < sections
        invariant
            result.len() == i,
            // All previously added sub-vectors have the correct length
            forall|k: int| 0 <= k < i ==> result[k].len() == section_len,
            // All elements in previously added sub-vectors are correctly assigned
            forall|k: int, j: int| 0 <= k < i && 0 <= j < section_len ==> result[k][j] == arr[k * (section_len as int) + j],
            i <= sections,
        decreases sections - i
    {
        let mut sub_vec: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < section_len
            invariant
                sub_vec.len() == j,
                // All elements in sub_vec are correctly assigned based on original arr
                forall|k: int| 0 <= k < j ==> sub_vec[k] == arr[(i * section_len + k) as int],
                j <= section_len,
            decreases section_len - j
        {
            let arr_idx = (i * section_len + j) as int;
            proof {
                assert(0 <= arr_idx);
                assert(arr_idx < arr.len());
            }
            sub_vec.push(arr[arr_idx]);
            j = j + 1;
        }
        result.push(sub_vec); // sub_vec now has length `section_len`
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}