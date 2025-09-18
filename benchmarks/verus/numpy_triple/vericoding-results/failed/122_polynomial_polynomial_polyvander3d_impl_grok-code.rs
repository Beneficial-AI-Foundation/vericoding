// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn poly_size(x_deg: usize, y_deg: usize, z_deg: usize) -> int {
    ((x_deg as int) + 1) * ((y_deg as int) + 1) * ((z_deg as int) + 1)
}

/* helper modified by LLM (iteration 4): added cast to int to support arithmetic operations in proof */
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|p: int| 0 <= p < result.len() ==> result[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using usize for exec code variables instead of int */
    let stride_z: usize = z_deg + 1;
    let stride_y: usize = stride_z * (y_deg + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < x.len() {
        invariant(result.len() == i);
        decreases(x.len() - i);
        assert(i < x.len());
        let mut row: Vec<f64> = Vec::new();
        let mut pow_x: f64 = 1.0;
        let mut xd: usize = 0;
        while xd <= x_deg {
            invariant(row.len() == (xd as int) * (stride_y as int));
            decreases((x_deg as int) + 1 - (xd as int));
            let mut pow_y: f64 = 1.0;
            let mut yd: usize = 0;
            while yd <= y_deg {
                invariant(row.len() == ((xd as int) * (stride_y as int)) + ((yd as int) * (stride_z as int)));
                decreases((y_deg as int) + 1 - (yd as int));
                let mut pow_z: f64 = 1.0;
                let mut zd: usize = 0;
                while zd <= z_deg {
                    invariant(row.len() == ((xd as int) * (stride_y as int)) + ((yd as int) * (stride_z as int)) + (zd as int));
                    decreases((z_deg as int) + 1 - (zd as int));
                    row.push(pow_x * pow_y * pow_z);
                    assert(i < z.len());
                    pow_z *= z[i];
                    zd += 1;
                }
                assert(i < y.len());
                pow_y *= y[i];
                yd += 1;
            }
            assert(i < x.len());
            pow_x *= x[i];
            xd += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}