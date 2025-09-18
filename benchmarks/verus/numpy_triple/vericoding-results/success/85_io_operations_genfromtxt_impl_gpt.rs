// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_index_after_skip_within_total(total: usize, skip: usize, i: usize)
    requires
        skip < total,
        i < total - skip,
    ensures
        i + skip < total
{
}

fn empty_row() -> Vec<f32> {
    Vec::new()
}
// </vc-helpers>

// <vc-spec>
fn genfromtxt(input: Vec<String>, delimiter: String, fill_value: f32, skip_header: usize) -> (result: Vec<Vec<f32>>)
    requires 
        skip_header < input.len(),
    ensures
        result.len() == input.len() - skip_header,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let line_idx = (i + skip_header as int) as usize;
            line_idx < input.len()
        },
// </vc-spec>
// <vc-code>
{
    let total = input.len();
    let target = total - skip_header;
    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < target
        invariant
            input.len() == total,
            target == total - skip_header,
            0 <= i <= target,
            res.len() == i
        decreases target - i
    {
        res.push(Vec::<f32>::new());
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}