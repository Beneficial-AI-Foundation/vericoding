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
    /* code modified by LLM (iteration 5): [pushed correct value from file.content to match invariant] */
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            result@ == file.content.subrange(offset as int, (offset + i) as int),
        decreases n - i
    {
        let val = file.content[offset + i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}