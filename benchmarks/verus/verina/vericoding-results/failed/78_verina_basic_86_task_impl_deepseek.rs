// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed wrap_index return type annotation and added result variable */
spec fn wrap_index(i: int, len: nat) -> (result: int)
    requires len > 0,
    ensures 0 <= result < len,
{
    let r = i % (len as int);
    if r >= 0 { r } else { r + (len as int) }
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
/* code modified by LLM (iteration 5): Fixed result variable initialization and loop */
{
    let len = a.len();
    let mut result = Vec::with_capacity(len);
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let src_idx = wrap_index(j + offset, len);
                result[j] == a[src_idx]
            },
        decreases len - i
    {
        let src_idx = wrap_index(i + offset, len);
        result.push(a[src_idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}