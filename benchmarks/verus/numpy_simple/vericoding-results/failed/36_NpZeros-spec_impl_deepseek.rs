// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compilation error - remove helper functions from code section */

/* helper modified by LLM (iteration 5): Fix recursive implementation to work with usize */
fn zeros_helper(n: usize) -> (result: Vec<i8>)
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == 0
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = zeros_helper(n - 1);
        v.push(0);
        v
    }
}

/* helper modified by LLM (iteration 5): Create row vector with zeros using usize */
fn create_zero_row(cols: usize) -> (result: Vec<i8>)
    ensures
        result@.len() == cols,
        forall|j: int| 0 <= j < cols ==> result@[j] == 0
{
    zeros_helper(cols)
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
/* code modified by LLM (iteration 5): Move main implementation code here */
{
    let result = zeros_helper(n);
    result
}
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            result@.len() == i,
            i <= rows,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == cols,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < cols ==> result@[k]@[j] == 0
        decreases rows - i
    {
        let row = create_zero_row(cols);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}