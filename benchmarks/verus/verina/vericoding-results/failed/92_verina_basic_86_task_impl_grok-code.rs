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
    /* code modified by LLM (iteration 4): Fixed compilation error by using tracked actual_offset to avoid using int in exec code and updated spec/indexing to use sequence views */
    let a_len = a.len();
    if a_len == 0 {
        return Vec::new();
    }
    proof {
        let actual_offset = offset % (a_len as int);
        // actual_offset satisfies 0 <= actual_offset < a_len as int
    }
    let actual_offset_usize = actual_offset as usize; // verifiable since actual_offset < a_len as int
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a_len
        invariant
            i <= a_len,
            result.len() == i,
            forall |j: nat| 
                j < i ==> {
                    let src_j = ((j as int) + actual_offset) % (a_len as int);
                    result@[j] == a@[src_j as usize]
                }
    {
        let src_idx = (i + actual_offset_usize) % a_len;
        result.push(a[src_idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}