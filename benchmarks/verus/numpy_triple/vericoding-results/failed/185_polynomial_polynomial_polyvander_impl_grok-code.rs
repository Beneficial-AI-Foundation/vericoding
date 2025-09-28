// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added (result: f32) to return type to fix compilation error with 'result' undefined */fn power(base: f32, exp: usize) -> (result: f32)
    requires true,
    ensures
        exp == 0 ==> result == 1.0f32,
        exp > 0 ==> result == power(base, exp - 1) * base,
    decreases exp
{
    if exp == 0 {
        1.0f32
    } else {
        power(base, exp - 1) * base
    }
}
// </vc-helpers>

// <vc-spec>
fn polyvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): unchanged from previous iteration, relies on fixed power helper */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == deg + 1,
            forall|k: int| 0 <= k < i ==> result[k][0] == 1.0f32,
            forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j <= deg ==> result[k][j] == power(x[k], j),
        decreases x.len() - i
    {
        let mut row = Vec::new();
        let mut p = 1.0f32;
        let mut j = 0;
        while j <= deg
            invariant
                j <= deg + 1,
                row.len() == j,
                p == power(x[i], j),
                forall|m: int| 0 <= m < j ==> row[m] == power(x[i], m),
            decreases deg - j
        {
            row.push(p);
            if j < deg {
                p = p * x[i];
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}