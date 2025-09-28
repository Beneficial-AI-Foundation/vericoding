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
// <vc-code>
/* code modified by LLM (iteration 4): fixed type issue, use usize for indexing in vec new lambda */
{
    Vec::new(a.len(), |i: usize| {
        let src_idx = ((i as int + offset) % (a.len() as int)) as usize;
        a[src_idx]
    })
}
// </vc-code>
// </vc-code>

}
fn main() {}