// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that offset + k is within sequence length given bounds */
proof fn seq_index_within_bounds(s: Seq<f64>, offset: usize, n: usize, k: usize)
    requires
        offset <= s.len(),
        s.len() - offset >= n,
        k < n,
    ensures
        offset + k < s.len(),
{
    assert(k < n);
    assert(offset + k < offset + n);
    assert(offset + n <= s.len());
    assert(offset + k < s.len());
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
/* code modified by LLM (iteration 5): copy n elements from file.content into result Vec using Seq.index to avoid int casts */
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> result[k] == file.content@[((offset + (k as usize)) as int)],
        decreases n - i
    {
        proof {
            seq_index_within_bounds(file.content, offset, n, i);
        }
        result.push(file.content.index(offset + i));
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}