// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermemulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() >= 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0,
        forall|i: int| 1 <= i < c.len() as int ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed initialization loop to avoid overflow and satisfy invariants] */
    let n = c.len();

    let mut result: Vec<f64> = Vec::new();
    result.push(0.0);
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k + 1,
            forall|j: int| 0 <= j < result.len() as int ==> result@[j] == 0.0,
        decreases n - k
    {
        result.push(0.0);
        k = k + 1;
    }

    if c.len() > 1 {
        let mut i: usize = 1;
        while i < c.len()
            invariant
                1 <= i && i <= c.len(),
                result.len() == c.len() + 1,
                result@[0] == 0.0,
                result@[1] == 0.0,
                forall|j: int| 1 <= j < i as int ==> result@[j + 1] == c@[j],
                forall|k_idx: int| (i + 1) as int <= k_idx <= c.len() as int ==> result@[k_idx] == 0.0,
            decreases c.len() - i
        {
            result.set(i + 1, c[i]);
            i = i + 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}