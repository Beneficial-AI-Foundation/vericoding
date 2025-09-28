// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof block from lemma - using direct assertions */
fn create_vec_with_size(size: usize) -> (result: Vec<f32>)
    ensures result.len() == size
{
    let mut vec = Vec::new();
    let mut i = 0;
    while i < size
        invariant
            i <= size,
            vec.len() == i,
        decreases size - i
    {
        vec.push(0.0);
        i += 1;
    }
    vec
}

proof fn lemma_division_bounds(total: usize, sections: usize, i: usize)
    requires
        sections > 0,
        total % sections == 0,
        i < sections,
    ensures
        i * (total / sections) + (total / sections) <= total,
        (i + 1) * (total / sections) <= total,
{
    let section_size = total / sections;
    assert(total == sections * section_size);
    assert(i + 1 <= sections);
    assert((i + 1) * section_size <= sections * section_size);
    assert((i + 1) * section_size <= total);
    assert(i * section_size + section_size == (i + 1) * section_size);
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
    /* code modified by LLM (iteration 5): simplified proof calls without proof blocks */
    let section_size = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut section_idx = 0;
    
    while section_idx < sections
        invariant
            section_idx <= sections,
            result.len() == section_idx,
            section_size == arr.len() / sections,
            sections > 0,
            arr.len() % sections == 0,
            forall|k: int| 0 <= k < section_idx ==> #[trigger] result[k].len() == section_size,
            forall|k: int, j: int| 0 <= k < section_idx && 0 <= j < section_size ==> 
                #[trigger] result[k][j] == arr[k * section_size + j],
        decreases sections - section_idx
    {
        let mut section = Vec::new();
        let mut elem_idx = 0;
        
        while elem_idx < section_size
            invariant
                elem_idx <= section_size,
                section.len() == elem_idx,
                section_idx < sections,
                section_size == arr.len() / sections,
                section_idx * section_size + elem_idx <= arr.len(),
                forall|j: int| 0 <= j < elem_idx ==> 
                    #[trigger] section[j] == arr[section_idx * section_size + j],
            decreases section_size - elem_idx
        {
            lemma_division_bounds(arr.len(), sections, section_idx);
            assert(section_idx * section_size + elem_idx < arr.len());
            section.push(arr[section_idx * section_size + elem_idx]);
            elem_idx += 1;
        }
        
        result.push(section);
        section_idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}