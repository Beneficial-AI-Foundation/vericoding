// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed loop invariants to hold after increments */
    let section_size = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < sections
        invariant
            i <= sections,
            result.len() == i,
            section_size == arr.len() / sections,
            sections > 0,
            arr.len() % sections == 0,
            i <= sections,
            forall|k: int| 0 <= k < i ==> result[k].len() == section_size,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < section_size ==> 
                result[k][j] == arr[k * section_size + j],
        decreases sections - i
    {
        let mut section: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        
        while j < section_size
            invariant
                j <= section_size,
                section.len() == j,
                i < sections,
                section_size == arr.len() / sections,
                arr.len() % sections == 0,
                i * section_size + section_size <= arr.len(),
                forall|k: int| 0 <= k < j ==> section[k] == arr[i * section_size + k],
            decreases section_size - j
        {
            section.push(arr[i * section_size + j]);
            j = j + 1;
        }
        
        result.push(section);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}