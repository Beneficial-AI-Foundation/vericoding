// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix predicate macro and use proper Verus syntax */
predicate expected_value_at_index(k: int, c: Seq<i8>, result: Seq<i8>) {
    0 <= k < result.len() ==> #[trigger] result[k] as int == 
        (if k == 0 { 0 } else { 0 }) + 
        (if k > 0 && k - 1 < c.len() { c[k - 1] as int / 2 } else { 0 }) + 
        (if k + 1 < c.len() { c[k + 1] as int * (k + 1) } else { 0 })
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
/* code modified by LLM (iteration 5): fix compilation errors and implement proper logic */
{
    let n = c.len();
    let mut result = Vec::with_capacity(n + 1);
    
    let mut k: usize = 0;
    while k < n + 1
        invariant
            result@.len() == k,
            result@.len() <= n + 1,
            forall|i: int| 0 <= i < k ==> expected_value_at_index(i, c@, result@),
        decreases (n + 1) - k
    {
        let val: i8 = {
            let k_int = k as int;
            let base_contribution = if k_int == 0 { 0 } else { 0 };
            let forward_contribution = if k_int > 0 && (k_int - 1) < n as int { 
                c[k - 1] as i32 / 2 
            } else { 
                0 
            };
            let backward_contribution = if k_int + 1 < n as int { 
                c[k + 1] as i32 * ((k_int + 1) as i32) 
            } else { 
                0 
            };
            (base_contribution + forward_contribution + backward_contribution) as i8
        };
        
        result.push(val);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}