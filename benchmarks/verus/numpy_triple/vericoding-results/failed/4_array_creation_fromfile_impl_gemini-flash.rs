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
/* code modified by LLM (iteration 5): Replaced `seq_view()` with `@` for `Seq` access */
{
    let mut result_vec = Vec::new();
    let mut i = 0usize;

    while i < n
        invariant
            i <= n,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == file.content@[offset + j],
    {
        result_vec.push(file.content@[offset + i]);
        i = i + 1;
    }
    proof {
        assert(n == result_vec.len());
    }
    result_vec
}
// </vc-code>

}
fn main() {}