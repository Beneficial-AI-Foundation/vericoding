// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): safe seq get to access file content as spec value */
fn seq_get(file: &FileData, idx: usize) -> f64 { file.content@[idx] }
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
    /* code modified by LLM (iteration 5): populate vector from file content using helper and use spec-level Vec view in invariants */
    let mut v: Vec<f64> = Vec::new();
    v.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant v.len() == i
        invariant forall|j: int| 0 <= j && j < i as int ==> (v@)@[j as usize] == file.content@[offset + (j as usize)]
        decreases n - i
    {
        let val: f64 = seq_get(file, offset + i);
        v.push(val);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}