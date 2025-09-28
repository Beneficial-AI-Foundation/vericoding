// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> result[j][1] == x[j]
    {
        let mut row: Vec<f32> = Vec::new();
        row.push(1.0f32);
        
        if deg > 0 {
            row.push(x[i]);
            let mut j: usize = 2;
            let mut power: f32 = x[i] * x[i];
            while j <= deg
                invariant
                    2 <= j <= deg + 1,
                    row.len() == j,
                    row[0] == 1.0f32,
                    row[1] == x[i],
                    power == vstd::arithmetic::power::pow(x[i], j as nat)
            {
                row.push(power);
                power = power * x[i];
                j = j + 1;
            }
        }
        
        assert(row.len() == deg + 1);
        assert(row[0] == 1.0f32);
        assert(deg > 0 ==> row[1] == x[i]);
        
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}