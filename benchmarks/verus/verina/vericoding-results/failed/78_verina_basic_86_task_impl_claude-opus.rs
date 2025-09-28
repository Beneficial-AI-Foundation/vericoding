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
    /* code modified by LLM (iteration 5): Fix type conversion issues - use as_int() for usize to int conversion */
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
        // Compute source index directly in spec mode for the proof
        let src_idx_spec = ((i as int) + offset) % (n as int);
        
        // For executable code, we need to handle the modulo operation
        // Since offset >= 0 and i >= 0, we know src_idx_spec >= 0
        // We can safely compute it as usize
        let src_idx = ((i as int + offset) % (n as int)) as usize;
        
        proof {
            // Prove that src_idx matches our spec
            assert(0 <= src_idx_spec < n as int);
            assert(src_idx == src_idx_spec as usize);
        }
        
        result.push(a[src_idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}