// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clauses to loops */
fn make_herme_row(x_i: f64, deg: usize) -> (row: Vec<f64>)
    requires deg >= 0
    ensures
        row.len() == deg + 1,
        row.view()[0] == 1.0,
        deg > 0 ==> row.view()[1] == x_i,
{
    let mut row: Vec<f64> = Vec::new();
    let mut k: usize = 0;
    while k < deg + 1
        invariant
            row.len() == k,
            k <= deg + 1,
        decreases (deg + 1) - k
    {
        row.push(0.0);
        k = k + 1;
    }

    row.set(0, 1.0);

    if deg > 0 {
        row.set(1, x_i);

        let mut j: usize = 2;
        let mut j_minus_1_f64: f64 = 1.0;
        while j <= deg
            invariant
                2 <= j <= deg + 1,
                row.len() == deg + 1,
                row.view()[0] == 1.0,
                row.view()[1] == x_i,
            decreases deg - j
        {
            let val = x_i * row[j - 1] - j_minus_1_f64 * row[j - 2];
            row.set(j, val);
            j = j + 1;
            j_minus_1_f64 = j_minus_1_f64 + 1.0;
        }
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to main loop */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            deg >= 0,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result.view()[k].len() == deg + 1,
            forall|k: int| 0 <= k < i ==> result.view()[k][0] == 1.0,
            deg > 0 ==> forall|k: int| 0 <= k < i ==> result.view()[k][1] == x.view()[k],
        decreases x.len() - i
    {
        let row = make_herme_row(x[i], deg);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}