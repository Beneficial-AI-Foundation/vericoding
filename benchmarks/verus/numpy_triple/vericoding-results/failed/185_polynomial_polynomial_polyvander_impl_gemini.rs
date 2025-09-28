// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed spec_power and weakened ensures on power */
fn power(base: f32, exp: usize) -> (result: f32)
    ensures
        exp == 0 ==> result == 1.0f32,
        exp == 1 ==> result == base,
{
    if exp == 0 {
        return 1.0f32;
    }
    
    let mut acc = base;
    let mut i: usize = 1;
    while i < exp
        invariant
            1 <= i <= exp,
        decreases exp - i
    {
        acc = acc * base;
        i = i + 1;
    }
    acc
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
    /* code modified by LLM (iteration 5): removed dependency on spec_power from invariants */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result@[j]@[0] == 1.0f32,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> result@[j]@[1] == x@[j],
        decreases x.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j <= deg
            invariant
                i < x.len(),
                0 <= j <= deg + 1,
                row.len() == j,
                j > 0 ==> row@[0] == 1.0f32,
                deg > 0 && j > 1 ==> row@[1] == x@[i as int],
            decreases (deg + 1) - j
        {
            row.push(power(x[i], j));
            j = j + 1;
        }

        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}