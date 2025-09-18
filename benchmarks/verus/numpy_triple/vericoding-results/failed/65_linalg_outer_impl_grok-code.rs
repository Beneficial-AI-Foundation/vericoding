// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i] * b[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant compilation error by splitting into multiple invariant lines */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let a_len: usize = a.len();
    let b_len: usize = b.len();
    let mut i: usize = 0;
    while i < a_len
        invariant 0 <= (i as int) <= (a_len as int)
        invariant (@result).len() == (i as int)
        invariant forall |k: int| 0 <= k < (i as int) ==> (@result)@[k].len() == (b_len as int)
        invariant forall |k: int, l: int| 0 <= k < (i as int) && 0 <= l < (b_len as int) ==> (@result)@[k][l] == a@[k] * b@[l]
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < b_len
            invariant 0 <= (j as int) <= (b_len as int)
            invariant (@row).len() == (j as int)
            invariant forall |m: int| 0 <= m < (j as int) ==> (@row)@[m] == a@[ (i as int) ] * b@[m]
        {
            row.push(a[i] * b[j]);
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