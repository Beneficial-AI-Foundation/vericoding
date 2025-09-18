// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified bounds checking helper for array access */
spec fn valid_index(arr_len: int, i: int, section_size: int, j: int) -> bool
{
    i >= 0 && section_size > 0 && j >= 0 && i * section_size + j < arr_len
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
{
    /* code modified by LLM (iteration 5): fixed bounds assertions and invariants for proper verification */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let section_size = arr.len() / sections;
    
    let mut i = 0;
    while i < sections
        invariant
            0 <= i <= sections,
            result.len() == i,
            section_size == arr.len() / sections,
            sections > 0,
            arr.len() % sections == 0,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == section_size,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < section_size ==> 
                k * section_size + j < arr.len() && #[trigger] result[k][j] == arr[k * section_size + j],
        decreases sections - i
    {
        let mut section: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < section_size
            invariant
                0 <= j <= section_size,
                section.len() == j,
                0 <= i < sections,
                section_size == arr.len() / sections,
                arr.len() % sections == 0,
                i * section_size < arr.len(),
                forall|idx: int| 0 <= idx < j ==> 
                    i * section_size + idx < arr.len() &&
                    #[trigger] section[idx] == arr[i * section_size + idx],
            decreases section_size - j
        {
            proof {
                assert(i < sections);
                assert(j < section_size);
                assert(section_size == arr.len() / sections);
                assert(arr.len() % sections == 0);
                assert(i * section_size + j < i * section_size + section_size);
                assert(i * section_size + section_size <= (i + 1) * section_size);
                assert((i + 1) * section_size <= sections * section_size);
                assert(sections * section_size == arr.len());
            }
            section.push(arr[i * section_size + j]);
            j += 1;
        }
        result.push(section);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}