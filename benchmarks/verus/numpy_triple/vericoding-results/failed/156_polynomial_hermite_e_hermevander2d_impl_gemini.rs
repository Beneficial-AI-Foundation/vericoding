// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence indexing in specs to use 'int' instead of 'usize'. */
fn compute_hermite_vec(t: i8, deg: usize) -> (result: Vec<i64>)
    ensures
        result.len() == deg + 1,
        forall|k: nat| (k as int) <= (deg as int) ==> result@[k as int] as int == hermite_basis(k, t as int),
{
    let mut v: Vec<i64> = Vec::new();
    v.push(1);
    if deg == 0 {
        return v;
    }
    v.push(t as i64);

    let mut i: usize = 2;
    while i <= deg
        invariant
            2 <= i <= deg + 1,
            v.len() == i,
            forall|k: nat| (k as int) < (i as int) ==> v@[k as int] as int == hermite_basis(k, t as int),
        decreases deg - i
    {
        proof {
            let k = i as nat;
            assert(hermite_basis(k, t as int) == t as int * hermite_basis((k - 1) as nat, t as int) - (k - 1) as int * hermite_basis((k - 2) as nat, t as int));
            assert(v@[(i - 1) as int] as int == hermite_basis((k - 1) as nat, t as int));
            assert(v@[(i - 2) as int] as int == hermite_basis((k - 2) as nat, t as int));
        }

        let h_prev1 = v[i-1];
        let h_prev2 = v[i-2];

        let val = (t as i64) * h_prev1 - (i as i64 - 1) * h_prev2;
        v.push(val);
        i = i + 1;
    }
    v
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
    /* code modified by LLM (iteration 5): No changes, only fixed compilation errors in helper function. */
    let mut vander: Vec<Vec<i8>> = Vec::new();
    let mut point_idx: usize = 0;
    while point_idx < x.len()
        invariant
            0 <= point_idx <= x.len(),
            vander.len() == point_idx,
            x.len() == y.len(),
            forall|i: int| 0 <= i < point_idx ==> vander@[i].len() == (x_deg + 1) * (y_deg + 1),
        decreases x.len() - point_idx
    {
        let xi = x[point_idx];
        let yi = y[point_idx];

        let hermite_x = compute_hermite_vec(xi, x_deg);
        let hermite_y = compute_hermite_vec(yi, y_deg);

        let mut row: Vec<i8> = Vec::new();
        let mut y_j: usize = 0;
        while y_j <= y_deg
            invariant
                0 <= y_j <= y_deg + 1,
                hermite_x.len() == x_deg + 1,
                hermite_y.len() == y_deg + 1,
                row.len() == y_j * (x_deg + 1),
            decreases y_deg - y_j
        {
            let mut x_k: usize = 0;
            while x_k <= x_deg
                invariant
                    0 <= x_k <= x_deg + 1,
                    hermite_x.len() == x_deg + 1,
                    hermite_y.len() == y_deg + 1,
                    row.len() == y_j * (x_deg + 1) + x_k,
                decreases x_deg - x_k
            {
                let val = hermite_x[x_k] * hermite_y[y_j];
                let val_i8 =
                    if (i8::MIN as i64) <= val && val <= (i8::MAX as i64) {
                        val as i8
                    } else {
                        0i8
                    };
                row.push(val_i8);
                x_k = x_k + 1;
            }
            y_j = y_j + 1;
        }

        proof {
            assert(row.len() == (y_deg + 1) * (x_deg + 1));
        }

        vander.push(row);
        point_idx = point_idx + 1;
    }

    vander
}
// </vc-code>

}
fn main() {}