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

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checks and indexing */
    let n = x.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg + 1),
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i ==> j < x.len() && result[j][1] == x[j],
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        
        if deg >= 0 {
            row.push(1.0f32);
        }
        
        if deg >= 1 {
            row.push(x[i]);
        }
        
        if deg >= 2 {
            let mut j: usize = 2;
            let mut prev: f32 = 1.0f32;
            let mut curr: f32 = x[i];
            
            while j <= deg
                invariant
                    2 <= j <= deg + 1,
                    row.len() == j,
                    row[0] == 1.0f32,
                    deg >= 1 ==> row[1] == x[i as int],
                decreases deg + 1 - j
            {
                let x_i = x[i];
                let next = 2.0f32 * x_i * curr - prev;
                row.push(next);
                prev = curr;
                curr = next;
                j = j + 1;
            }
        }
        
        assert(row.len() == (deg + 1));
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}