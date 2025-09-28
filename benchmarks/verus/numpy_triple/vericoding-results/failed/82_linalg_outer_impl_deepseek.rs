// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type casting to use usize in ghost code */
fn inner_prod(a: &Vec<i8>, b: &Vec<i8>, i: int, j: int) -> (prod: i8)
    requires
        0 <= i < a.len(),
        0 <= j < b.len(),
    ensures
        prod as int == (a[i] as int) * (b[j] as int),
{
    let ai = a[i];
    let bj = b[j];
    ai * bj
}
// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<Vec<i8>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] as int == a[i] as int * b[j] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix while loop conditions to use usize instead of int */
{
    let mut result: Vec<Vec<i8>> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == b.len(),
            forall|k: int, l: int| 0 <= k < result.len() && 0 <= l < result[k].len() ==> 
                result[k][l] as int == (a[k] as int) * (b[l] as int),
        decreases a.len() - i,
    {
        let mut row: Vec<i8> = Vec::with_capacity(b.len());
        let mut j: usize = 0;
        while j < b.len()
            invariant
                row.len() == j,
                forall|l: int| 0 <= l < row.len() ==> row[l] as int == (a[i] as int) * (b[l] as int),
            decreases b.len() - j,
        {
            let prod = inner_prod(&a, &b, i as int, j as int);
            row.push(prod);
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