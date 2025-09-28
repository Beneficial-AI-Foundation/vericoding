// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed hermite_basis_exec by naming return value */
fn hermite_basis_exec(k: usize, t: i8) -> (result: i8)
    ensures
        result as int == hermite_basis(k as nat, t as int),
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let prev1 = hermite_basis_exec(k - 1, t);
        let prev2 = hermite_basis_exec(k - 2, t);
        t * prev1 - ((k - 1) as i8) * prev2
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
    /* code modified by LLM (iteration 4): Added decreases clauses to all while loops */
    let n = x.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            result.len() == i,
            forall|point_idx: int| 0 <= point_idx < i ==> 
                result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut xi: usize = 0;
        
        while xi <= x_deg
            invariant
                row.len() == xi * (y_deg + 1),
            decreases x_deg + 1 - xi
        {
            let mut yi: usize = 0;
            
            while yi <= y_deg
                invariant
                    row.len() == xi * (y_deg + 1) + yi,
                decreases y_deg + 1 - yi
            {
                let hx = hermite_basis_exec(xi, x[i]);
                let hy = hermite_basis_exec(yi, y[i]);
                let val = hx * hy;
                row.push(val);
                yi = yi + 1;
            }
            xi = xi + 1;
        }
        
        assert(row.len() == (x_deg + 1) * (y_deg + 1));
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}