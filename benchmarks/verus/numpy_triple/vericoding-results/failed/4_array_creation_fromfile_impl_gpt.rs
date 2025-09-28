// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add trivial lemma to satisfy helpers section */
proof fn lemma_trivial()
    ensures
        true,
{
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
    /* code modified by LLM (iteration 2): Construct result from the appropriate subrange using ghost Seq */
    let ghost s: Seq<f64> = file.content.subrange(offset as int, (offset + n) as int);
    let v: Vec<f64> = Vec::from_seq(s);
    v
}
// </vc-code>

}
fn main() {}