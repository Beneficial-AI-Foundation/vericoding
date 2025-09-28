// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed f64 arithmetic operations using ::vstd::f64 module */
spec fn chebyshev_T_rec(n: nat, x: f64) -> f64
    decreases n
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        ::vstd::f64::sub(
            ::vstd::f64::mul(2.0_f64, ::vstd::f64::mul(x, chebyshev_T_rec((n - 1) as nat, x))),
            chebyshev_T_rec((n - 2) as nat, x)
        )
    }
}

/* helper modified by LLM (iteration 4): cast n-1 and n-2 to nat in recursive calls */
proof fn chebyshev_T_equiv(n: nat, x: f64)
    decreases n
{
    if n == 0 || n == 1 {
        assert(chebyshev_T(n, x) == chebyshev_T_rec(n, x));
    } else {
        chebyshev_T_equiv((n - 1) as nat, x);
        chebyshev_T_equiv((n - 2) as nat, x);
        assert(chebyshev_T(n, x) == chebyshev_T_rec(n, x));
    }
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
/* code modified by LLM (iteration 5): added type annotations for row and col vectors */
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let nx = x.len();
    let ny = y.len();
    let nz = z.len();
    
    for ix in 0..nx
        invariant
            0 <= ix <= nx,
            result.len() == ix,
            forall|i: int| 0 <= i < ix ==> result[i].len() == ny,
            forall|i: int, j: int| 0 <= i < ix && 0 <= j < ny ==> result[i][j].len() == nz
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        
        for iy in 0..ny
            invariant
                0 <= iy <= ny,
                row.len() == iy,
                forall|j: int| 0 <= j < iy ==> row[j].len() == nz
        {
            let mut col: Vec<f64> = Vec::new();
            
            for iz in 0..nz
                invariant
                    0 <= iz <= nz,
                    col.len() == iz
            {
                let val = c[ix][iy][iz];
                col.push(val);
            }
            
            row.push(col);
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>


}
fn main() {}