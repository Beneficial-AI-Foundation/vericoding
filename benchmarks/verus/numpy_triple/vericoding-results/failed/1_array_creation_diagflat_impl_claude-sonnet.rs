// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking helper for vector access */
spec fn valid_index(i: int, len: int) -> bool {
    0 <= i < len
}
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> #[trigger] result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
    let mut result = Vec::new();
    let n = v.len();
    
    for i in 0..n
        invariant
            result.len() == i * n,
            forall|row: int, col: int| 0 <= row < i && 0 <= col < n ==>
                #[trigger] if row == col {
                    result@[row * n + col] == v@[row]
                } else {
                    result@[row * n + col] == 0.0f32
                }
    {
        for j in 0..n
            invariant
                result.len() == i * n + j,
                forall|row: int, col: int| 0 <= row < i && 0 <= col < n ==>
                    #[trigger] if row == col {
                        result@[row * n + col] == v@[row]
                    } else {
                        result@[row * n + col] == 0.0f32
                    },
                forall|col: int| 0 <= col < j ==>
                    #[trigger] if i == col {
                        result@[i * n + col] == v@[i as int]
                    } else {
                        result@[i * n + col] == 0.0f32
                    }
        {
            if i == j {
                result.push(v[i]);
            } else {
                result.push(0.0f32);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}