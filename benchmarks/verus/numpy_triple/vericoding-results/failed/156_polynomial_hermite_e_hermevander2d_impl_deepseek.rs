// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatch in recursive call */
proof fn hermite_basis_monotonic(k: nat, t: int)
    requires
        k >= 2,
        t >= 0,
    ensures
        hermite_basis(k, t) >= hermite_basis((k - 1) as nat, t),
    decreases k
{
    if k == 2 {
        assert(hermite_basis(2, t) == t * hermite_basis(1, t) - 1 * hermite_basis(0, t));
        assert(hermite_basis(2, t) == t * t - 1);
        assert(hermite_basis(1, t) == t);
        assert(t * t - 1 >= t) by {
            assert(t * t - t - 1 >= 0);
        };
    } else {
        hermite_basis_monotonic((k - 1) as nat, t);
        assert(hermite_basis(k, t) == t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t));
        assert(hermite_basis((k - 1) as nat, t) == t * hermite_basis((k - 2) as nat, t) - (k - 2) as int * hermite_basis((k - 3) as nat, t));
        assert(hermite_basis(k, t) - hermite_basis((k - 1) as nat, t) == 
               (t - 1) * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t) + (k - 2) as int * hermite_basis((k - 3) as nat, t));
    }
}

fn compute_hermite_basis(k: u32, t: i8) -> (result: i8)
    requires
        k <= 10,
    ensures
        result as int == hermite_basis(k as nat, t as int),
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let prev1 = compute_hermite_basis(k - 1, t);
        let prev2 = compute_hermite_basis(k - 2, t);
        (t as i16 * prev1 as i16 - (k - 1) as i16 * prev2 as i16) as i8
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(k: nat, t: int) -> int
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t)
    }
}

fn hermevander2d(x: Vec<i8>, y: Vec<i8>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error with proper type handling */
    let n = x.len();
    let basis_size = (x_deg + 1) * (y_deg + 1);
    let mut result = Vec::<Vec<i8>>::new();
    
    let mut point_idx: usize = 0;
    while point_idx < n
        invariant
            point_idx <= n,
            result.len() == point_idx,
            forall|i: int| 0 <= i < point_idx ==> result[i].len() == basis_size,
    {
        let mut basis_row = Vec::<i8>::new();
        
        let mut i_deg: usize = 0;
        while i_deg <= x_deg
            invariant
                i_deg <= x_deg + 1,
                basis_row.len() == i_deg * (y_deg + 1),
        {
            let mut j_deg: usize = 0;
            while j_deg <= y_deg
                invariant
                    j_deg <= y_deg + 1,
                    basis_row.len() == i_deg * (y_deg + 1) + j_deg,
            {
                let x_val = x[point_idx];
                let y_val = y[point_idx];
                
                let h_x = compute_hermite_basis(i_deg as u32, x_val);
                let h_y = compute_hermite_basis(j_deg as u32, y_val);
                
                basis_row.push(h_x * h_y);
                j_deg += 1;
            }
            i_deg += 1;
        }
        
        result.push(basis_row);
        point_idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}