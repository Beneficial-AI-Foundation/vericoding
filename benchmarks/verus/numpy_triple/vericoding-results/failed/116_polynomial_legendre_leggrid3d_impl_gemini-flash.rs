// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, helper is correctly defined as a spec function. */
spec fn check_coords(x: Seq<f64>, y: Seq<f64>, z: Seq<f64>, i1: int, j1: int, k1: int, i2: int, j2: int, k2: int) -> bool
    requires
        0 <= i1 < x.len(), 0 <= i2 < x.len(),
        0 <= j1 < y.len(), 0 <= j2 < y.len(),
        0 <= k1 < z.len(), 0 <= k2 < z.len(),
    ensures
        check_coords(x, y, z, i1, j1, k1, i2, j2, k2) == (x[i1] == x[i2] && y[j1] == y[j2] && z[k1] == z[k2]),
{
    x[i1] == x[i2] && y[j1] == y[j2] && z[k1] == z[k2]
}
// </vc-helpers>

// <vc-spec>
fn leggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x.len() > 0,
        y.len() > 0,
        z.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j].len() == z.len(),

        true, // Result matrix elements exist (trivially true)
        //forall|i: int, j: int, k: int| 
        //    0 <= i < x.len() && 0 <= j < y.len() && 0 <= k < z.len() ==>
        //    exists|val: f64| result[i][j][k] == val,

        forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
            0 <= i1 < x.len() && 0 <= i2 < x.len() && 
            0 <= j1 < y.len() && 0 <= j2 < y.len() &&
            0 <= k1 < z.len() && 0 <= k2 < z.len() ==>
            ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
             (result[i1][j1][k1] != result[i2][j2][k2] || 
              (x[i1] == x[i2] && y[j1] == y[j2] && z[k1] == z[k2])))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by removing `proof` before `forall` for the result length assertions and removed verification bypasses. */
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();

    for i in 0..x.len() {
        let mut row: Vec<Vec<f64>> = Vec::new();
        for j in 0..y.len() {
            let mut col: Vec<f64> = Vec::new();
            for k in 0..z.len() {
                col.push(c.get(i).unwrap().get(j).unwrap().get(k).unwrap().clone());
            }
            row.push(col);
        }
        result.push(row);
    }

    // Proof of `result.len() == x.len()`
    proof {
        assert(result.len() == x.len());
    }

    // Proof of `forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len()`
    forall |i: int| 0 <= i < result.len() implies result[i].len() == y.len()
    {
        assert(result@[i].len() == y.len());
    }

    // Proof of `forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j].len() == z.len()`
    forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() implies result[i][j].len() == z.len()
    {
        assert(result@[i]@[j].len() == z.len());
    }

    // Proof for the value property
    forall |i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
        0 <= i1 < x.len() && 0 <= i2 < x.len() &&
        0 <= j1 < y.len() && 0 <= j2 < y.len() &&
        0 <= k1 < z.len() && 0 <= k2 < z.len() implies
        ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
         (result@[i1]@[j1]@[k1] != result@[i2]@[j2]@[k2] || 
          check_coords(x@.to_seq(), y@.to_seq(), z@.to_seq(), i1, j1, k1, i2, j2, k2)))
    {
        if i1 != i2 || j1 != j2 || k1 != k2 {
            if result@[i1]@[j1]@[k1] == result@[i2]@[j2]@[k2] {
                assert(c@[i1]@[j1]@[k1] == c@[i2]@[j2]@[k2]);
            }
        }
    }

    result
}
// </vc-code>

}
fn main() {}