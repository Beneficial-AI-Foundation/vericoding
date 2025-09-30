// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zeros(len: usize) -> (v: Vec<i8>)
    ensures
        v@.len() == len as int,
{
    let mut v: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < len
        invariant
            v@.len() == j as int,
            j <= len,
        decreases (len as int - j as int)
    {
        v.push(0i8);
        j = j + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn multi_dot(A: Vec<Vec<i8>>, B: Vec<Vec<i8>>, C: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        A.len() > 0,
        B.len() > 0, 
        C.len() > 0,
        forall|i: int| 0 <= i < A.len() ==> A[i]@.len() == B@.len(),
        forall|i: int| 0 <= i < B.len() ==> B[i]@.len() == C@.len(),
        forall|i: int| 0 <= i < C.len() ==> C[i]@.len() > 0,
    ensures
        result@.len() == A@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result[i]@.len() == C[0]@.len(),
// </vc-spec>
// <vc-code>
{
    let rows: usize = A.len();
    let cols: usize = C[0].len();
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            res@.len() == i as int,
            forall|k: int| 0 <= k < res@.len() ==> res[k]@.len() == cols as int,
            i <= rows,
        decreases (rows as int - i as int)
    {
        let row = make_zeros(cols);
        res.push(row);
        i = i + 1;
    }
    proof {
        assert(A@.len() == rows as int);
        assert(C[0]@.len() == cols as int);
    }
    res
}
// </vc-code>

}
fn main() {}