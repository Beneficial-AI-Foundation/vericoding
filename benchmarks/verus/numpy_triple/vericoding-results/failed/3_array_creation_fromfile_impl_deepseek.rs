// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct FileData {
    pub content: Seq<f64>,
    pub valid: bool,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic int cast helper and added proper ghost conversion */
proof fn lemma_seq_index_property_usize(s: Seq<f64>, idx: usize) ensures s@[idx] == s[idx as int] {}
spec fn validate_n_count(n: usize, count: i32) -> bool { (count == (n as i32)) || (count == -1) }
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
/* code modified by LLM (iteration 5): fixed integer casting by using usize arithmetic with ghost conversion */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == file.content@[offset + j],
    {
        proof { lemma_seq_index_property_usize(file.content, offset + i); }
        let value = file.content[offset + i as int];
        result.push(value);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}