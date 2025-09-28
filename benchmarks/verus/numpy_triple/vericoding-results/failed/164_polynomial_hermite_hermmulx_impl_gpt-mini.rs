// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use spec-level Vec sequence (c@) to index with int and return as int */
spec fn vec_get_i8_as_int(c: Vec<i8>, i: int) -> int
    requires
        0 <= i, i < c.len(),
{
    c@[i as nat] as int
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
    /* code modified by LLM (iteration 5): implement hermmulx with runtime i64 arithmetic and spec uses vec_get_i8_as_int in invariant */
    let n = c.len();
    let mut res: Vec<i8> = Vec::new();
    res.reserve(n + 1);
    let mut i: nat = 0;
    while i < n + 1
        invariant
            res.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] res[k] as int == {
                let base_contribution: int = 0;
                let forward_contribution: int = if k > 0 && k - 1 < n as int {
                    vec_get_i8_as_int(c, k - 1) / 2
                } else {
                    0
                };
                let backward_contribution: int = if k + 1 < n as int {
                    vec_get_i8_as_int(c, k + 1) * (k + 1)
                } else {
                    0
                };
                base_contribution + forward_contribution + backward_contribution
            },
        decreases (n + 1) - i
    {
        let forward_i64: i64 = if i > 0 {
            let idx = i - 1;
            if idx < n { (c[idx] as i64) / 2 } else { 0 }
        } else { 0 };
        let backward_i64: i64 = if i + 1 < n { (c[i + 1] as i64) * ((i + 1) as i64) } else { 0 };
        let val_i64: i64 = forward_i64 + backward_i64;
        res.push(val_i64 as i8);
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}