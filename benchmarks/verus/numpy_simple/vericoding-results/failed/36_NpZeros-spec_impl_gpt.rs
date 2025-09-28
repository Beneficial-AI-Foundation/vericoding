// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): transitivity of range bounds: if 0 <= j < k and k <= n, then 0 <= j < n */
proof fn range_subset_trans(j: int, k: int, n: int)
    requires
        0 <= j,
        j < k,
        k <= n,
    ensures
        0 <= j < n,
{
    assert(0 <= j);
    assert(j < n);
}
// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (result: Vec<i8>)
    ensures 
        result@.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == 0
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn zeros2d(rows: usize, cols: usize) -> (result: Vec<Vec<i8>>)
    ensures 
        result@.len() == rows,
        forall|i: int| 0 <= i < rows ==> result@[i]@.len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> result@[i]@[j] == 0
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct vectors of zeros using loops with invariants */
    let mut v: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k as int <= n as int,
            v@.len() == k as int,
            forall|j: int| 0 <= j < v@.len() ==> v@[j] == 0,
        decreases n as int - k as int
    {
        v.push(0i8);
        k = k + 1;
    }
    v
}
{
    /* code modified by LLM (iteration 5): build 2D zeros by pushing rows created with zeros(cols) */
    let mut v: Vec<Vec<i8>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r as int <= rows as int,
            v@.len() == r as int,
            forall|i: int| 0 <= i < v@.len() ==> v@[i]@.len() == cols as int,
            forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < cols as int ==> v@[i]@[j] == 0,
        decreases rows as int - r as int
    {
        let row: Vec<i8> = zeros(cols);
        v.push(row);
        r = r + 1;
    }
    v
}
// </vc-code>


}
fn main() {}