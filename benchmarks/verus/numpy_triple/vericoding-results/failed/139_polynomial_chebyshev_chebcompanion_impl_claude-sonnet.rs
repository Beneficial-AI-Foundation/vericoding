// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking for vector access */
    let n = c.len() - 1;
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j].len() == n,
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut k = 0;
        
        while k < n
            invariant
                k <= n,
                row.len() == k,
                n < c.len(),
                k < c.len(),
            decreases n - k
        {
            if i == 0 {
                if k == 1 {
                    row.push(1.0);
                } else {
                    row.push(0.0);
                }
            } else if i == n - 1 {
                if k == i {
                    row.push(-c[0] / c[n as usize]);
                } else {
                    if k + 1 < c.len() {
                        row.push(-c[k + 1] / c[n as usize]);
                    } else {
                        row.push(0.0);
                    }
                }
            } else {
                if k == i + 1 {
                    row.push(0.5);
                } else if k == i - 1 {
                    row.push(0.5);
                } else {
                    row.push(0.0);
                }
            }
            k += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}