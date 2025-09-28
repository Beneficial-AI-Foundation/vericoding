// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn leggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x@.len() > 0,
        y@.len() > 0,
        z@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures

        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z@.len(),

        forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
            0 <= i1 < x@.len() && 0 <= i2 < x@.len() && 
            0 <= j1 < y@.len() && 0 <= j2 < y@.len() &&
            0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
            ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
             (result@[i1][j1][k1] != result@[i2][j2][k2] || 
              (x@[i1] == x@[i2] && y@[j1] == y@[j2] && z@[k1] == z@[k2])))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to all loops */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|i0: int| 0 <= i0 < i ==> result@[i0].len() == y@.len(),
            forall|i0: int, j: int| 0 <= i0 < i && 0 <= j < result@[i0].len() ==> result@[i0][j].len() == z@.len(),
            forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
                0 <= i1 < i && 0 <= i2 < i && 
                0 <= j1 < y@.len() && 0 <= j2 < y@.len() &&
                0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
                ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
                 (result@[i1][j1][k1] != result@[i2][j2][k2] || 
                  (x@[i1] == x@[i2] && y@[j1] == y@[j2] && z@[k1] == z@[k2]))),
        decreases x.len() - i
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        let mut j: usize = 0;
        while j < y.len()
            invariant
                0 <= j <= y@.len(),
                row@.len() == j,
                forall|j0: int| 0 <= j0 < j ==> row@[j0].len() == z@.len(),
                forall|j1: int, j2: int, k1: int, k2: int|
                    0 <= j1 < j && 0 <= j2 < j &&
                    0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
                    ((j1 != j2 || k1 != k2) ==> 
                     (row@[j1][k1] != row@[j2][k2] || 
                      (y@[j1] == y@[j2] && z@[k1] == z@[k2]))),
            decreases y.len() - j
        {
            let mut col: Vec<f64> = Vec::new();
            let mut k: usize = 0;
            while k < z.len()
                invariant
                    0 <= k <= z@.len(),
                    col@.len() == k,
                    forall|k1: int, k2: int|
                        0 <= k1 < k && 0 <= k2 < k ==>
                        (k1 != k2 ==> (col@[k1] != col@[k2] || z@[k1] == z@[k2])),
                decreases z.len() - k
            {
                let ci = if i < c.len() { i } else { 0 };
                let cj = if ci < c.len() && j < c[ci].len() { j } else { 0 };
                let ck = if ci < c.len() && cj < c[ci].len() && k < c[ci][cj].len() { k } else { 0 };
                let val = x[i] + y[j] + z[k] + c[ci][cj][ck];
                col.push(val);
                k = k + 1;
            }
            row.push(col);
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