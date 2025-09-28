// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change needed as the helper is already correct. */
pub fn float_eq(a: f64, b: f64) -> bool {
    a == b
}
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
/* code modified by LLM (iteration 5): Corrected type mismatches (nat vs int) in sequence indexing arguments and fixed `_nat` suffixes. Also ensured correct indexing into nested `Vec`s within `c`. */
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let x_len: nat = x@.len();
    let y_len: nat = y@.len();
    let z_len: nat = z@.len();

    let c_len: nat = c@.len();
    let c_inner_len_y: nat = c@[0].len();
    let c_inner_len_z: nat = c@[0][0].len();

    proof {
        assert(x_len > 0);
        assert(y_len > 0);
        assert(z_len > 0);
        assert(c_len > 0);
    }

    let mut i: nat = 0;
    while i < x_len
        invariant
            0 <= i <= x_len,
            result@.len() == i,
            forall|idx: int| 0 <= idx < i ==> result@[idx]@.len() == (y_len as int),
            forall|idx: int, jdx: int| 0 <= idx < i && 0 <= jdx < (y_len as int) ==> result@[idx][jdx]@.len() == (z_len as int),
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        let mut j: nat = 0;
        while j < y_len
            invariant
                0 <= j <= y_len,
                row@.len() == j,
                forall|jdx: int| 0 <= jdx < j ==> row@[jdx]@.len() == (z_len as int),
        {
            let mut col: Vec<f64> = Vec::new();
            let mut k: nat = 0;
            while k < z_len
                invariant
                    0 <= k <= z_len,
                    col@.len() == k,
            {
                let mut sum_val: f64 = 0.0;
                let mut ci: nat = 0;
                while ci < c_len
                    invariant
                        0 <= ci <= c_len,
                        ci < c_len ==> c@[ci].len() == c_inner_len_y,
                        ci < c_len && c_inner_len_y > 0 ==> c@[ci][0].len() == c_inner_len_z,
                {
                    let mut cj: nat = 0;
                    while cj < c_inner_len_y
                        invariant
                            0 <= cj <= c_inner_len_y,
                            ci < c_len,
                            cj < c_inner_len_y ==> c@[ci][cj].len() == c_inner_len_z,
                    {
                        let mut ck: nat = 0;
                        while ck < c_inner_len_z
                            invariant
                                0 <= ck <= c_inner_len_z,
                                ci < c_len,
                                cj < c_inner_len_y,
                        {
                            sum_val = sum_val + x@[i as int] * y@[j as int] * z@[k as int] * c@[ci as int][cj as int][ck as int];
                            ck = ck + 1 as nat;
                        }
                        cj = cj + 1 as nat;
                    }
                    ci = ci + 1 as nat;
                }
                col.push(sum_val);
                k = k + 1 as nat;
            }
            row.push(col);
            j = j + 1 as nat;
        }
        result.push(row);
        i = i + 1 as nat;
    }

    result
}
// </vc-code>

}
fn main() {}