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
    /* code modified by LLM (iteration 5): fix type casting for offset modulo operation */
    let n = a.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let src_idx = (j + offset) % (n as int);
                #[trigger] result[j] == a[src_idx]
            },
    {
        let ghost src_idx_int = ((i as int) + offset) % (n as int);
        let offset_mod = (offset % (n as int)) as usize;
        let src_idx_usize = (i + offset_mod) % n;
        
        proof {
            assert(src_idx_usize as int == src_idx_int);
        }
        
        result.push(a[src_idx_usize]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}