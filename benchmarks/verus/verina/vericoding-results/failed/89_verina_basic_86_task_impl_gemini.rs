// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed incorrect path for lemma_mod_properties */
proof fn lemma_rotated_idx_in_bounds(idx: int, offset: int, len: int)
    requires
        len > 0,
        0 <= idx < len,
        offset >= 0,
    ensures
        0 <= (idx + offset) % len < len,
{
    vstd::arithmetic::mod_p::lemma_mod_properties(idx + offset, len);
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
    /* code modified by LLM (iteration 2): changed loop to use usize and fixed ghost/exec type mismatches */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result = Vec::new_with_len(n, 0i32);
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            a.len() == n,
            result.len() == n,
            offset >= 0,
            forall|j: int| 0 <= j < (i as int) ==> {
                let src_idx = (j + offset) % (n as int);
                #[trigger] result@[j] == a@[src_idx]
            },
    {
        proof {
            lemma_rotated_idx_in_bounds(i as int, offset, n as int);
        }
        
        let src_idx = (((i as int) + offset) % (n as int)) as usize;
        let val = a[src_idx];
        result.set(i, val);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}