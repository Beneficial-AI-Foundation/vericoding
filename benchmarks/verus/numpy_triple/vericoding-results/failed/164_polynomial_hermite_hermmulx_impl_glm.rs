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
/* code modified by LLM (iteration 3): handle usize overflow and use i128 arithmetic */
{
    let n = c.len();
    let result_len = if n == usize::MAX { 0 } else { n + 1 };
    let mut result = Vec::with_capacity(result_len);
    for i in 0..result_len {
        let base_contribution: i128 = 0;
        let forward_contribution: i128 = if i > 0 && i - 1 < n { 
            (c[i - 1] as i128) / 2
        } else { 
            0
        };
        let backward_contribution: i128 = if i + 1 < n { 
            (c[i + 1] as i128) * ((i + 1) as i128)
        } else { 
            0
        };
        let value = base_contribution + forward_contribution + backward_contribution;
        result.push(value as i8);
    }
    result
}
// </vc-code>


}
fn main() {}