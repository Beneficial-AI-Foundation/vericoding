// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): moved inner loop and strengthened its invariants */
    let mut c: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            c.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> c[j].len() == (deg + 1) as int,
            forall|j: int| 0 <= j < i as int ==> c[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i as int ==> c[j][1] == x[j],
        decreases x.len() - i
    {
        let mut row: Vec<Vec<f32>> = Vec::new();
        row.push(1.0f32);

        if deg >= 1 {
            row.push(x[i]);
            let mut j: usize = 2;
            while j <= deg
                invariant
                    i < x.len(),
                    deg >= 1,
                    2 <= j <= deg + 1,
                    row.len() == j as int,
                    row[0] == 1.0f32,
                    row[1] == x[i as int],
                decreases deg - j
            {
                let val = 2.0f32 * x[i] * row[j - 1] - row[j - 2];
                row.push(val);
                j = j + 1;
            }
        }

        c.push(row);
        i = i + 1;
    }
    c
}
// </vc-code>

}
fn main() {}