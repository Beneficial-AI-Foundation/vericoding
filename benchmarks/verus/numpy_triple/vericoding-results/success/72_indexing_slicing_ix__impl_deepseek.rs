// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added decreases clause to while loops */
fn ix_seq1(seq1: &Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == seq1.len(),
        forall|i: int| 0 <= i < seq1.len() ==> result[i].len() == 1,
        forall|i: int| 0 <= i < seq1.len() ==> result[i][0] == seq1@[i]
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0;
    while i < seq1.len()
        invariant
            0 <= i <= seq1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == 1,
            forall|k: int| 0 <= k < i ==> result[k][0] == seq1@[k]
        decreases seq1.len() - i
    {
        let mut inner_vec = Vec::new();
        inner_vec.push(seq1[i]);
        result.push(inner_vec);
        i += 1;
    }
    result
}

fn ix_seq2(seq2: &Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == 1,
        result[0].len() == seq2.len(),
        forall|j: int| 0 <= j < seq2.len() ==> result[0][j] == seq2@[j]
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut inner_vec: Vec<i32> = Vec::new();
    let mut j = 0;
    while j < seq2.len()
        invariant
            0 <= j <= seq2.len(),
            inner_vec.len() == j,
            forall|k: int| 0 <= k < j ==> inner_vec[k] == seq2@[k]
        decreases seq2.len() - j
    {
        inner_vec.push(seq2[j]);
        j += 1;
    }
    result.push(inner_vec);
    result
}
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
/* code modified by LLM (iteration 3): No changes needed to main code */
{
    let seq1_vec = ix_seq1(&seq1);
    let seq2_vec = ix_seq2(&seq2);
    (seq1_vec, seq2_vec)
}
// </vc-code>

}
fn main() {}