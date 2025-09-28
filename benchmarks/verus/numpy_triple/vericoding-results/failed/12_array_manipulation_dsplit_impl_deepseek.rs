// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Added trigger annotations to quantifiers */
proof fn lemma_div_mod(x: int, d: int)
    requires
        d > 0,
        x >= 0,
    ensures
        x == d * (x / d) + (x % d),
        x % d >= 0,
        x % d < d,
{
    // Proof of division and modulo properties
}

proof fn lemma_vec_slice_properties<T>(v: Vec<T>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len <= v.len(),
    ensures
        (#[trigger] v@.subrange(start, start + len)).len() == len,
        forall|i: int| 0 <= i < len ==> #[trigger] v@.subrange(start, start + len)[i] == v@[start + i],
{
    // Proof of vector subrange properties
}

fn vec_subrange<T: Clone>(v: &Vec<T>, start: usize, len: usize) -> (result: Vec<T>)
    requires
        start <= v.len(),
        len <= v.len() - start,
    ensures
        result@ == v@.subrange(start as int, (start + len) as int),
{
    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == v@[start as int + j],
        decreases
            len - i,
    {
        result.push(v[start + i].clone());
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 5): Added proof blocks to establish vector properties */
    let section_size = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(sections);
    let mut i: usize = 0;
    
    proof {
        lemma_div_mod(arr.len() as int, sections as int);
    }
    
    while i < sections
        invariant
            i <= sections,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == section_size,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < section_size ==> 
                #[trigger] result[k][j] == arr@[k * section_size + j],
        decreases
            sections - i,
    {
        let start_index = i * section_size;
        proof {
            lemma_vec_slice_properties(arr, start_index as int, section_size as int);
        }
        let slice = vec_subrange(&arr, start_index, section_size);
        result.push(slice);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}