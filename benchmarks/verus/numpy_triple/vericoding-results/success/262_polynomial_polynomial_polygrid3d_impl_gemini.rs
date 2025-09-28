// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polygrid3d(
    x: Vec<i8>, 
    y: Vec<i8>, 
    z: Vec<i8>,
    c: Vec<Vec<Vec<i8>>>
) -> (result: Vec<Vec<Vec<i8>>>)
    requires 
        x@.len() > 0,
        y@.len() > 0, 
        z@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z@.len()
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<Vec<i8>>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|ii: int| 0 <= ii < i ==> result@[ii].len() == y.len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < y.len() ==> result@[ii]@[jj].len() == z.len(),
        decreases x.len() - i
    {
        let mut plane: Vec<Vec<i8>> = Vec::new();
        let mut j: usize = 0;
        while j < y.len()
            invariant
                0 <= j <= y.len(),
                plane@.len() == j,
                forall|jj: int| 0 <= jj < j ==> plane@[jj].len() == z.len(),
            decreases y.len() - j
        {
            let mut row: Vec<i8> = Vec::new();
            let mut k: usize = 0;
            while k < z.len()
                invariant
                    0 <= k <= z.len(),
                    row@.len() == k,
                decreases z.len() - k
            {
                row.push(0i8);
                k = k + 1;
            }
            plane.push(row);
            j = j + 1;
        }
        result.push(plane);
        i = i + 1;
    }
    let _ = c;
    result
}
// </vc-code>


}
fn main() {}