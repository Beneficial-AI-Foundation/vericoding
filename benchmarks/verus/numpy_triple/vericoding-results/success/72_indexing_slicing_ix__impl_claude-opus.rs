// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ix_(seq1: Vec<i32>, seq2: Vec<i32>) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires 
        seq1.len() > 0,
        seq2.len() > 0,
    ensures 

        result.0.len() == seq1.len(),
        forall|i: int| 0 <= i < seq1.len() ==> result.0[i].len() == 1,
        forall|i: int| 0 <= i < seq1.len() ==> result.0[i][0] == seq1[i],

        result.1.len() == 1,
        result.1[0].len() == seq2.len(),
        forall|j: int| 0 <= j < seq2.len() ==> result.1[0][j] == seq2[j],

        forall|i: int, j: int| 0 <= i < seq1.len() && 0 <= j < seq2.len() ==> 
            result.0[i][0] == seq1[i] && result.1[0][j] == seq2[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to loops */
    let mut result0: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < seq1.len()
        invariant
            i <= seq1.len(),
            result0.len() == i,
            forall|k: int| 0 <= k < i ==> result0[k].len() == 1,
            forall|k: int| 0 <= k < i ==> result0[k][0] == seq1[k],
        decreases seq1.len() - i
    {
        let mut inner: Vec<i32> = Vec::new();
        inner.push(seq1[i]);
        result0.push(inner);
        i = i + 1;
    }
    
    let mut result1: Vec<Vec<i32>> = Vec::new();
    let mut row: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < seq2.len()
        invariant
            j <= seq2.len(),
            row.len() == j,
            forall|k: int| 0 <= k < j ==> row[k] == seq2[k],
        decreases seq2.len() - j
    {
        row.push(seq2[j]);
        j = j + 1;
    }
    result1.push(row);
    
    (result0, result1)
}
// </vc-code>

}
fn main() {}