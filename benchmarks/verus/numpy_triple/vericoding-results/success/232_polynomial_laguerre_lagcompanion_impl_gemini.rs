// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// The logic for constructing the companion matrix is straightforward and self-contained,
// so no helper functions are necessary.
// </vc-helpers>

// <vc-spec>
fn lagcompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let m = n - 1;
    let mut result: Vec<Vec<i8>> = Vec::new();

    let mut i: usize = 0;
    while i < m
        invariant
            m == c.len() - 1,
            c.len() >= 2,
            0 <= i <= m,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k].len() == m as nat,
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                m == c.len() - 1,
                i < m,
                0 <= j <= m,
                row.len() == j,
            decreases m - j
        {
            if i < m - 1 {
                if j == i + 1 {
                    row.push(1);
                } else {
                    row.push(0);
                }
            } else {
                row.push(c[j]);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}