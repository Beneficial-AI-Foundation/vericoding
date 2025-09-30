// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_i8() -> i8 {
    0i8
}
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
            i <= x.len(),
            result@.len() == i as int,
            forall|ii: int| 0 <= ii < result@.len() ==> result@[ii]@.len() == y@.len(),
            forall|ii: int, jj: int| 0 <= ii < result@.len() && 0 <= jj < result@[ii]@.len() ==> result@[ii]@[jj]@.len() == z@.len(),
        decreases x@.len() - i as int
    {
        let mut mid: Vec<Vec<i8>> = Vec::new();
        let mut j: usize = 0;
        while j < y.len()
            invariant
                j <= y.len(),
                mid@.len() == j as int,
                forall|jj: int| 0 <= jj < mid@.len() ==> mid@[jj]@.len() == z@.len(),
            decreases y@.len() - j as int
        {
            let mut row: Vec<i8> = Vec::new();
            let mut k: usize = 0;
            while k < z.len()
                invariant
                    k <= z.len(),
                    row@.len() == k as int,
                decreases z@.len() - k as int
            {
                row.push(0i8);
                k = k + 1;
            }
            mid.push(row);
            j = j + 1;
        }
        result.push(mid);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}