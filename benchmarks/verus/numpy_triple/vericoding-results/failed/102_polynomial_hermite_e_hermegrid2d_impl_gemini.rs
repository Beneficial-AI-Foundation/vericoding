// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermegrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> (
            (c.len() == 0 || (exists|k: int| 0 <= k < c.len() && c[k].len() == 0) ==> result[i][j] == 0.0f32)
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Combined loop invariants to provide necessary context for proofs and used nat indices. */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: nat = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: nat| k < i ==> {
                &&& (#[trigger] result@[k]).len() == y.len()
                &&& forall|l: nat| l < y.len() ==>
                    (c.len() == 0 || (exists|m: nat| m < c.len() && c@[m].len() == 0)) ==>
                        result@[k]@[l] == 0.0f32
            },
        decreases x.len() - i
    {
        let mut row = Vec::new();
        let mut j: nat = 0;
        while j < y.len()
            invariant
                j <= y.len(),
                row.len() == j,
                forall|k: nat| k < j ==> (c.len() == 0 || (exists|l: nat| l < c.len() && c@[l].len() == 0) ==> row@[k] == 0.0f32),
            decreases y.len() - j
        {
            row.push(0.0f32);
            j = j + 1;
        }
        assert(row.len() == y.len());
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}