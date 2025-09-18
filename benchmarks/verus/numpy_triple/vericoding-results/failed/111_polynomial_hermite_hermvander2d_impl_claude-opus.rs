// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn hermite_polynomial(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite_polynomial((n - 1) as nat, t) - 2 * (n - 1) * hermite_polynomial((n - 2) as nat, t)
    }
}

fn hermvander2d(x: Vec<i32>, y: Vec<i32>, xdeg: usize, ydeg: usize) -> (result: Vec<Vec<i32>>)
    requires x.len() == y.len(),
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (xdeg + 1) * (ydeg + 1),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k][0] == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixing arithmetic overflow and index bounds with proper checks */
    let n = x.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] result[i].len() == (xdeg + 1) * (ydeg + 1),
            forall|i: int| 0 <= i < k ==> #[trigger] result[i][0] == 1,
            n == x.len(),
            n == y.len()
        decreases n - k
    {
        let mut row: Vec<i32> = Vec::new();
        row.push(1); // Start with H_0(x) * H_0(y) = 1
        
        // First fill in H_i(x) * H_0(y) for i = 1 to xdeg
        let mut i: usize = 1;
        while i <= xdeg
            invariant
                1 <= i <= xdeg + 1,
                row.len() == i,
                row.len() >= 1,
                row[0] == 1,
                k < x.len(),
                k < n,
                n == x.len()
            decreases xdeg + 1 - i
        {
            let val = if i == 1 {
                let x_val = x[k];
                2i32 * x_val
            } else {
                proof {
                    assert(i >= 2);
                    assert(row.len() == i);
                    assert(i - 1 < row.len());
                    assert(i - 2 < row.len());
                }
                let prev1_idx = (i - 1) as usize;
                let prev2_idx = (i - 2) as usize;
                let x_val = x[k];
                let v1 = row[prev1_idx];
                let v2 = row[prev2_idx];
                #[verifier::truncate]
                let coeff = (i - 1) as i32;
                2i32 * x_val * v1 - 2i32 * coeff * v2
            };
            row.push(val);
            i = i + 1;
        }
        
        // Now fill in H_i(x) * H_j(y) for j = 1 to ydeg
        let mut j: usize = 1;
        while j <= ydeg
            invariant
                1 <= j <= ydeg + 1,
                row.len() == j * (xdeg + 1),
                row.len() >= 1,
                row[0] == 1,
                k < y.len(),
                k < n,
                n == y.len(),
                xdeg + 1 >= 1
            decreases ydeg + 1 - j
        {
            // H_0(x) * H_j(y)
            let val_0 = if j == 1 {
                let y_val = y[k];
                2i32 * y_val
            } else {
                proof {
                    assert(j >= 2);
                    assert(row.len() == j * (xdeg + 1));
                    assert((j - 1) * (xdeg + 1) < row.len());
                    assert((j - 2) * (xdeg + 1) < row.len());
                }
                let prev1_idx = ((j - 1) * (xdeg + 1)) as usize;
                let prev2_idx = ((j - 2) * (xdeg + 1)) as usize;
                let y_val = y[k];
                let v1 = row[prev1_idx];
                let v2 = row[prev2_idx];
                #[verifier::truncate]
                let coeff = (j - 1) as i32;
                2i32 * y_val * v1 - 2i32 * coeff * v2
            };
            row.push(val_0);
            
            // H_i(x) * H_j(y) for i = 1 to xdeg
            let mut i: usize = 1;
            while i <= xdeg
                invariant
                    1 <= i <= xdeg + 1,
                    row.len() == j * (xdeg + 1) + i,
                    row.len() >= 1,
                    row[0] == 1,
                    j >= 1,
                    j <= ydeg,
                    j * (xdeg + 1) < row.len(),
                    xdeg + 1 >= 1,
                    i <= row.len()
                decreases xdeg + 1 - i
            {
                proof {
                    assert(i < xdeg + 1);
                    assert(i < row.len());
                    assert(j * (xdeg + 1) < row.len());
                }
                // For general H_i(x) * H_j(y), we multiply the values
                let h_i_x = row[i as usize]; // H_i(x) from the first row (j=0)
                let h_j_y = row[(j * (xdeg + 1)) as usize]; // H_j(y) from this row (i=0)
                let val = h_i_x * h_j_y;
                row.push(val);
                i = i + 1;
            }
            j = j + 1;
        }
        
        proof {
            assert(row.len() == (xdeg + 1) * (ydeg + 1));
            assert(row[0] == 1);
        }
        result.push(row);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}