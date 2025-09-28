// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): made all helper functions spec functions to allow int type usage */
spec fn compute_base_contribution(k: int) -> int {
    if k == 0 { 0 } else { 0 }
}

spec fn compute_forward_contribution(c: Vec<i8>, k: int) -> int {
    if k > 0 && k - 1 < c.len() {
        c[k - 1] as int / 2
    } else {
        0
    }
}

spec fn compute_backward_contribution(c: Vec<i8>, k: int) -> int {
    if k + 1 < c.len() {
        c[k + 1] as int * (k + 1)
    } else {
        0
    }
}

spec fn compute_result_value(c: Vec<i8>, k: int) -> int {
    let base_contribution = compute_base_contribution(k);
    let forward_contribution = compute_forward_contribution(c, k);
    let backward_contribution = compute_backward_contribution(c, k);
    base_contribution + forward_contribution + backward_contribution
}

fn safe_add_length(len: usize) -> (result: usize)
    requires len < usize::MAX
    ensures result == len + 1
{
    len + 1
}
// </vc-helpers>

// <vc-spec>
fn hermmulx(c: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == c.len() + 1,
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] as int == {
            let base_contribution: int = if k == 0 { 0 } else { 0 };
            let forward_contribution: int = if k > 0 && k - 1 < c.len() { 
                c[k - 1] as int / 2
            } else { 
                0
            };
            let backward_contribution: int = if k + 1 < c.len() { 
                c[k + 1] as int * (k + 1)
            } else { 
                0
            };
            base_contribution + forward_contribution + backward_contribution
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax error */
    
    let new_len = safe_add_length(c.len());
    let mut result = Vec::with_capacity(new_len);
    let mut i: usize = 0;
    
    while i < new_len
        invariant
            result.len() == i,
            i <= c.len() + 1,
            new_len == c.len() + 1,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k] as int == {
                let base_contribution: int = if k == 0 { 0 } else { 0 };
                let forward_contribution: int = if k > 0 && k - 1 < c.len() { 
                    c[k - 1] as int / 2
                } else { 
                    0
                };
                let backward_contribution: int = if k + 1 < c.len() { 
                    c[k + 1] as int * (k + 1)
                } else { 
                    0
                };
                base_contribution + forward_contribution + backward_contribution
            },
        decreases new_len - i
    {
        let base_contribution = if i == 0 { 0 } else { 0 };
        let forward_contribution = if i > 0 && i - 1 < c.len() {
            (c[i - 1] as i32) / 2
        } else {
            0
        };
        let backward_contribution = if i < c.len() - 1 {
            (c[i + 1] as i32) * ((i + 1) as i32)
        } else {
            0
        };
        
        let value = base_contribution + forward_contribution + backward_contribution;
        result.push(#[verifier::truncate] (value as i8));
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}