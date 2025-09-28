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
fn zeros(n: usize) -> (result: Vec<i8>)
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == 0
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 0
        decreases n - i
    {
        result.push(0);
        i += 1;
    }
    result
}

fn zeros2d(rows: usize, cols: usize) -> (result: Vec<Vec<i8>>)
    ensures
        result@.len() == rows,
        forall|i: int| 0 <= i < rows ==> result@[i]@.len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> result@[i]@[j] == 0
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < rows
        invariant
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == cols && forall|l: int| 0 <= l < cols ==> result@[k]@[l] == 0
        decreases rows - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        while j < cols
            invariant
                row@.len() == j,
                forall|m: int| 0 <= m < j ==> row@[m] == 0
            decreases cols - j
        {
            row.push(0);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}