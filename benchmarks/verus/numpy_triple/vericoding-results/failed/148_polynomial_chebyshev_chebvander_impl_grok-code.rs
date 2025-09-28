// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): rewrote inner loop initialization and removed with_capacity to fix invariant and overflow errors */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall |k: int| 0 <= k < i ==> result@[k].len() == deg + 1,
            forall |k: int| 0 <= k < i ==> result@[k]@[0] == 1.0f32,
            deg >= 1 ==> forall |k: int| 0 <= k < i ==> result@[k]@[1] == x@[k],
        decreases x.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut t_minus2: f32 = 0.0;
        let mut t_minus1: f32 = 1.0;
        row.push(t_minus1);
        if deg >= 1 {
            t_minus1 = x[i];
            t_minus2 = row[0];
            row.push(t_minus1);
        }
        let mut j = 2;
        while j <= deg
        {
            let next_t = 2.0 * x[i] * t_minus1 - t_minus2;
            row.push(next_t);
            t_minus2 = t_minus1;
            t_minus1 = next_t;
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result

// </vc-code>

}
fn main() {}