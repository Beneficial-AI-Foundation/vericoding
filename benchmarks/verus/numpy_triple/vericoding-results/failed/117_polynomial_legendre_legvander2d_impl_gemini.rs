// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added decreases clause to prove loop termination. */
fn legval(x: f64, deg: usize) -> (c: Vec<f64>)
    ensures
        c.len() == deg + 1,
        c.len() > 0 ==> c[0] == 1.0,
{
    if deg == 0 {
        return vec![1.0];
    }
    let mut c = Vec::with_capacity(deg + 1);
    c.push(1.0);
    c.push(x);
    let mut i: usize = 1;
    let mut i_f: f64 = 1.0;
    while i < deg
        invariant
            1 <= i <= deg,
            c.len() == i + 1,
            c[0] == 1.0,
        decreases deg - i
    {
        let p_next = ((2.0 * i_f + 1.0) * x * c[i] - i_f * c[i-1]) / (i_f + 1.0);
        c.push(p_next);
        i += 1;
        i_f += 1.0;
    }
    c
}
// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: usize, deg_y: usize) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clauses to all while loops to prove termination. */
    let mut v: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] v[j].len() == (deg_x + 1) * (deg_y + 1),
            forall|j: int| 0 <= j < i && v[j].len() > 0 ==> #[trigger] v[j][0] == 1.0,
        decreases x.len() - i
    {
        let c_x = legval(x[i], deg_x);
        let c_y = legval(y[i], deg_y);

        let mut row = Vec::new();
        let mut j: usize = 0;
        while j <= deg_x
            invariant
                j <= deg_x + 1,
                row.len() == j * (deg_y + 1),
            decreases (deg_x + 1) - j
        {
            let mut k: usize = 0;
            while k <= deg_y
                invariant
                    k <= deg_y + 1,
                    row.len() == j * (deg_y + 1) + k,
                decreases (deg_y + 1) - k
            {
                row.push(c_x[j] * c_y[k]);
                k += 1;
            }
            j += 1;
        }

        if row.len() > 0 {
            // The first element pushed corresponds to j=0, k=0.
            // This is c_x[0] * c_y[0].
            // Verus can track that row[0] retains this value.
            // From legval ensures, c_x[0]==1.0 and c_y[0]==1.0.
            // The SMT solver can verify 1.0 * 1.0 == 1.0.
            assert(row[0] == 1.0);
        }

        v.push(row);
        i += 1;
    }
    v
}
// </vc-code>

}
fn main() {}