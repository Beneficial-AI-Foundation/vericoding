// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Used a while loop with invariant to construct the Vec and ensure the elements are correct. */
    let mut result: Vec<f64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            result.len() == i,
            0 <= i <= n,
            forall |j: int| 0 <= j < i ==> result@[j] == file.content[(offset as int) + j]
    {
        result.push(file.content[(offset as int) + i]);
        i = i + 1;
    }
    assert(result.len() == n);
    result
}
// </vc-code>

}
fn main() {}