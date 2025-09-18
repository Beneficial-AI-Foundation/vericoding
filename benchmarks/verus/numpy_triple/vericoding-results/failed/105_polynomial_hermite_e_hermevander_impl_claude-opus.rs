// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add decreases clause to all loops */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = x.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result[j as int][0 as int] == 1.0,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> result[j as int][1 as int] == x[j as int]
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        
        while j <= deg
            invariant
                j <= deg + 1,
                row.len() == j,
                j > 0 ==> row[0 as int] == 1.0,
                j > 1 && deg > 0 ==> row[1 as int] == x[i as int]
            decreases deg + 1 - j
        {
            if j == 0 {
                row.push(1.0);
            } else if j == 1 {
                row.push(x[i]);
            } else {
                let prev1 = row[j - 1];
                let prev2 = row[j - 2];
                let mut factor: f64 = 0.0;
                let mut k: usize = 0;
                while k < j - 1
                    invariant k <= j - 1
                    decreases j - 1 - k
                {
                    factor = factor + 2.0;
                    k = k + 1;
                }
                row.push(x[i] * prev1 - factor * prev2);
            }
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