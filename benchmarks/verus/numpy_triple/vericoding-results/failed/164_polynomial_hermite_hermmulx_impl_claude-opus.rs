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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let n = c.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i <= n
        invariant
            i <= n + 1,
            result.len() == i,
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
        decreases n + 1 - i
    {
        let base_contribution: i8 = if i == 0 { 0 } else { 0 };
        let forward_contribution: i8 = if i > 0 && i - 1 < n { 
            c[i - 1] / 2
        } else { 
            0
        };
        let backward_contribution: i8 = if i + 1 < n { 
            c[i + 1] * ((i + 1) as i8)
        } else { 
            0
        };
        let value = base_contribution + forward_contribution + backward_contribution;
        result.push(value);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}