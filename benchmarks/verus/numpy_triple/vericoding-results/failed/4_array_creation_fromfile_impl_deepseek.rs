// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed usize_to_int function syntax */
fn idx_len_inbounds(file: &FileData, offset: usize, n: usize) -> ()
    requires
        offset <= file.content.len(),
        offset + n <= file.content.len(),
    ensures
        forall|i: int| 0 <= i < n ==> offset + i < file.content.len(),
{
    assert(forall|i: int| 0 <= i < n ==> offset + i < offset + n);
    assert(offset + n <= file.content.len());
    assert(forall|i: int| 0 <= i < n ==> offset + i < file.content.len());
}

fn usize_to_int(i: usize) -> (result: int)
    ensures
        result == i as int,
{
    i as int
}
// </vc-helpers>

// <vc-spec>
fn fromfile(n: usize, file: &FileData, count: i32, offset: usize) -> (result: Vec<f64>)
    requires 
        file.valid == true,
        count == (n as i32) || count == -1,
        offset <= file.content.len(),
        file.content.len() - offset >= n,
    ensures 
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == file.content[offset + i],
        n <= file.content.len() - offset,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type handling and loop indexing */
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    
    proof {
        idx_len_inbounds(file, offset, n);
    }
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == file.content[offset + j],
    {
        let val = file.content[offset + i];
        result.push(val);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}