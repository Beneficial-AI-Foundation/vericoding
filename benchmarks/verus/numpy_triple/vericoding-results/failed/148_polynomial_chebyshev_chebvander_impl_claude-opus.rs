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
{
    /* code modified by LLM (iteration 3): added decreases clause to inner loop */
    let n = x.len();
    let mut v: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j].len() == (deg + 1),
            forall|j: int| 0 <= j < i ==> v[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i ==> v[j][1] == x@[j],
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        row.push(1.0f32);
        
        if deg >= 1 {
            row.push(x[i]);
            
            let mut j: usize = 2;
            while j <= deg
                invariant
                    row.len() == j,
                    row[0] == 1.0f32,
                    row[1] == x@[i as int],
                    2 <= j <= deg + 1,
                decreases deg - j
            {
                let prev1 = row[(j - 1) as usize];
                let prev2 = row[(j - 2) as usize];
                let next_val = 2.0f32 * x[i] * prev1 - prev2;
                row.push(next_val);
                j = j + 1;
            }
        }
        
        v.push(row);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}