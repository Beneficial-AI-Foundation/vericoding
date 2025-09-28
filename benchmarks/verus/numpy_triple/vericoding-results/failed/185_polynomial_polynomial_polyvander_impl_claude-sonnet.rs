// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed parameter type from int to usize for compatibility */
fn pow_f32(base: f32, exp: usize) -> f32
    decreases exp
{
    if exp == 0 {
        1.0f32
    } else {
        base * pow_f32(base, exp - 1)
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
    /* code modified by LLM (iteration 5): fixed index type casting issues */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> result[j][1] == x[j]
    {
        let mut row = Vec::new();
        let mut k = 0;
        while k <= deg
            invariant
                k <= deg + 1,
                row.len() == k,
                k > 0 ==> row[0] == 1.0f32,
                k > 1 && deg > 0 ==> row[1] == x[i]
        {
            if k == 0 {
                row.push(1.0f32);
            } else if k == 1 {
                row.push(x[i]);
            } else {
                let base = x[i];
                let mut power = 1.0f32;
                let mut exp = 0;
                while exp < k
                    invariant
                        exp <= k,
                        power == pow_f32(base, exp)
                {
                    if exp > 0 {
                        power = power * base;
                    }
                    exp = exp + 1;
                }
                row.push(power);
            }
            k = k + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}