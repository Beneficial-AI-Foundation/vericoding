// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Implementation for zeros function */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 0
    {
        result.push(0i8);
        i = i + 1;
    }
    result
}

{
    /* code modified by LLM (iteration 5): Implementation for zeros2d function */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == cols,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < cols ==> result@[k]@[j] == 0
    {
        let mut row = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                row@.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == 0
        {
            row.push(0i8);
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