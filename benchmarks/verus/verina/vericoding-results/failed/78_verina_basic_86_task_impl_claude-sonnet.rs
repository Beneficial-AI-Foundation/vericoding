// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove requires/ensures from spec function */
spec fn safe_mod(i: int, offset: int, len: int) -> int
{
    (i + offset) % len
}
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
    /* code modified by LLM (iteration 5): calculate source index directly in executable code */
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(a.len());
    let len = a.len();
    
    for i in 0..len
        invariant
            result.len() == i,
            len == a.len(),
            forall|j: int| 0 <= j < i ==> {
                let src_idx = (j + offset) % (a.len() as int);
                result[j] == a[src_idx]
            },
    {
        let i_int = i as int;
        let len_int = len as int;
        let offset_mod = offset % len_int;
        let src_idx_int = (i_int + offset_mod) % len_int;
        let src_idx = src_idx_int as usize;
        result.push(a[src_idx]);
    }
    
    result
}
// </vc-code>

}
fn main() {}