// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): [use usize loop counter to fix compilation errors] */
    let mut result: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k <= c.len()
        invariant
            result.len() == k,
            k <= c.len() + 1,
            forall|i: int| 0 <= i < k as int ==> #[trigger] result@[i as nat] as int == {
                let forward_contribution: int = if i > 0 && i - 1 < c.len() as int {
                    c@[(i - 1) as nat] as int / 2
                } else {
                    0
                };
                let backward_contribution: int = if i + 1 < c.len() as int {
                    c@[(i + 1) as nat] as int * (i + 1)
                } else {
                    0
                };
                forward_contribution + backward_contribution
            },
        decreases (c.len() + 1) - k
    {
        let mut forward_contribution: i128 = 0;
        if k > 0 {
            forward_contribution = (c[k - 1] as i128) / 2;
        }

        let mut backward_contribution: i128 = 0;
        if k + 1 < c.len() {
            backward_contribution = (c[k + 1] as i128) * ((k + 1) as i128);
        }

        let value = forward_contribution + backward_contribution;
        result.push(value as i8);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}