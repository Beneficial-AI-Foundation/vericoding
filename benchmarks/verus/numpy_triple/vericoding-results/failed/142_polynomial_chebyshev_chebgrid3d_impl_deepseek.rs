// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed f64 multiplication syntax using Verus operators */
proof fn chebyshev_recursive_lemma(n: nat, x: f64)
    requires
        n >= 2,
    ensures
        chebyshev_T(n, x) == (2.0_f64 * x) * chebyshev_T((n - 1) as nat, x) - chebyshev_T((n - 2) as nat, x)
{
    if n == 2 {
        assert(chebyshev_T(2, x) == (2.0_f64 * x) * x - 1.0) by {
            reveal(chebyshev_T);
        };
        assert((2.0_f64 * x) * chebyshev_T(1, x) - chebyshev_T(0, x) == (2.0_f64 * x) * x - 1.0);
    } else {
        chebyshev_recursive_lemma((n - 1) as nat, x);
    }
}

spec fn chebyshev_correct(n: nat, x: f64) -> bool {
    if n == 0 {
        chebyshev_T(n, x) == 1.0
    } else if n == 1 {
        chebyshev_T(n, x) == x
    } else {
        chebyshev_T(n, x) == (2.0_f64 * x) * chebyshev_T((n - 1) as nat, x) - chebyshev_T((n - 2) as nat, x)
    }
}

proof fn initialize_chebyshev_T()
    ensures
        forall|x: f64| chebyshev_correct(0, x),
        forall|x: f64| chebyshev_correct(1, x)
{
    assert forall|x: f64| chebyshev_correct(0, x) by {
        reveal(chebyshev_T);
    };
    assert forall|x: f64| chebyshev_correct(1, x) by {
        reveal(chebyshev_T);
    };
}
// </vc-helpers>

// <vc-spec>
spec fn chebyshev_T(n: nat, x: f64) -> f64 
    decreases n
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        0.0
    }
}

fn chebgrid3d(
    x: Vec<f64>, 
    y: Vec<f64>, 
    z: Vec<f64>,
    c: Vec<Vec<Vec<f64>>>
) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x.len() > 0,
        y.len() > 0, 
        z.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
    ensures
        result.len() == x.len(),
        forall|ix: int| 0 <= ix < result.len() ==> result[ix].len() == y.len(),
        forall|ix: int, iy: int| 0 <= ix < result.len() && 0 <= iy < result[ix].len() ==> result[ix][iy].len() == z.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed vec indexing using proper integer types */
{
    let nx = x.len();
    let ny = y.len();
    let nz = z.len();
    let mut result = Vec::<Vec<Vec<f64>>>::new();
    let mut ix: int = 0;
    while ix < nx
        invariant
            ix <= nx,
            result.len() == ix,
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == ny,
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j].len() == nz
    {
        let mut row = Vec::<Vec<f64>>::new();
        let mut iy: int = 0;
        while iy < ny
            invariant
                iy <= ny,
                row.len() == iy,
                forall|j: int| 0 <= j < row.len() ==> row[j].len() == nz
        {
            let mut col = Vec::<f64>::new();
            let mut iz: int = 0;
            while iz < nz
                invariant
                    iz <= nz,
                    col.len() == iz
            {
                let mut sum = 0.0_f64;
                let mut c_outer_index: int = 0;
                while c_outer_index < c.len()
                    invariant
                        c_outer_index <= c.len()
                {
                    let outer_vec = c.index(c_outer_index);
                    let mut c_mid_index: int = 0;
                    while c_mid_index < outer_vec.len()
                        invariant
                            c_mid_index <= outer_vec.len()
                    {
                        let mid_vec = outer_vec.index(c_mid_index);
                        let mut c_inner_index: int = 0;
                        while c_inner_index < mid_vec.len()
                            invariant
                                c_inner_index <= mid_vec.len()
                        {
                            let c_inner = mid_vec.index(c_inner_index);
                            let t_ix_val = if ix == 0 { 1.0_f64 } else if ix == 1 { x.index(ix) } else { (2.0_f64 * x.index(ix)) * x.index(ix) - 1.0_f64 };
                            let t_iy_val = if iy == 0 { 1.0_f64 } else if iy == 1 { y.index(iy) } else { (2.0_f64 * y.index(iy)) * y.index(iy) - 1.0_f64 };
                            let t_iz_val = if iz == 0 { 1.0_f64 } else if iz == 1 { z.index(iz) } else { (2.0_f64 * z.index(iz)) * z.index(iz) - 1.0_f64 };
                            sum += c_inner * t_ix_val * t_iy_val * t_iz_val;
                            c_inner_index += 1;
                        }
                        c_mid_index += 1;
                    }
                    c_outer_index += 1;
                }
                col.push(sum);
                iz += 1;
            }
            row.push(col);
            iy += 1;
        }
        result.push(row);
        ix += 1;
    }
    result
}
// </vc-code>


}
fn main() {}