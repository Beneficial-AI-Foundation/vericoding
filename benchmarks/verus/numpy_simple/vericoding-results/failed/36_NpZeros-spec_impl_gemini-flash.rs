// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the extra new line in the helper function signature that made it consumed by the compiler, also added decreases clause. */
fn zeros_vec(len: usize) -> (result: Vec<i8>)
    ensures
        result@.len() == len,
        forall|i: int| 0 <= i < len ==> result@[i] == 0
{
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == 0,
            i <= len,
        decreases len - i
    {
        v.push(0);
        i = i + 1;
    }
    v
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
/* code modified by LLM (iteration 5): fixed compilation errors by changing the helper function's signature and implementing `decreases` clause. */
{
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> result@[k]@[l] == 0,
            i <= rows,
        decreases rows - i
    {
        let row_vec = zeros_vec(cols);

        result.push(row_vec);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}