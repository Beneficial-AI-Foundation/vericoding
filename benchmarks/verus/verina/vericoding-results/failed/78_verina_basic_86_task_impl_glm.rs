// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize for reduced offset */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }
    let offset_usize = offset as usize;
    let reduced_offset = offset_usize % n;
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[(j + offset) % (n as int)],
        decreases a.len() - i
    {
        let src_idx = (i + reduced_offset) % n;
        result.push(a[src_idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}