// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed int cast and used usize directly for indexing */
fn fromfile_helper(n: usize, file: &FileData, offset: usize) -> (result: Vec<f64>)
    requires
        file.valid == true,
        offset <= file.content.len(),
        file.content.len() - offset >= n,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == file.content[offset + i],
        n <= file.content.len() - offset,
{
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == file.content[offset + j],
            n <= file.content.len() - offset,
        decreases n - i
    {
        proof {
            let elem = file.content@[offset + i];
            result.push(elem);
        }
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 4): using fixed helper function with proof block */
{
    let result = fromfile_helper(n, file, offset);
    result
}
// </vc-code>

}
fn main() {}