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
    /* code modified by LLM (iteration 5): Fixed compilation errors by replacing sequence indexing @[ ] with Vec indexing [] in the executable code body for correct access to Vec elements. */
    let mut result: Vec<i8> = Vec::with_capacity(c.len() + 1);
    let result_len: usize = c.len() + 1;
    let mut i: usize = 0;
    while i < result_len
        invariant
            i as nat <= (result_len as nat),
            result.len() as nat == i as nat,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] result@[k] as int == {
                let base_contribution: int = if k == 0 { 0 } else { 0 };
                let forward_contribution: int = if k > 0 && k - 1 < c.len() {
                    c@[k - 1] as int / 2
                } else {
                    0
                };
                let backward_contribution: int = if k + 1 < c.len() {
                    c@[k + 1] as int * (k + 1)
                } else {
                    0
                };
                base_contribution + forward_contribution + backward_contribution
            },
        decreases (result_len - i) as nat,
    {
        let k: usize = i;
        let forward_contribution: i32 = if k > 0 && k - 1 < c.len() {
            (c[k - 1] as i32) / 2
        } else {
            0
        };
        let backward_contribution: i32 = if k + 1 < c.len() {
            (c[k + 1] as i32) * ((k + 1) as i32)
        } else {
            0
        };
        let total_contribution: i32 = forward_contribution + backward_contribution;
        result.push(total_contribution as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}