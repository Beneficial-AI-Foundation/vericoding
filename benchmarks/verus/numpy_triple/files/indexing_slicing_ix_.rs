use vstd::prelude::*;

verus! {

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
{
    assume(false);
    unreached();
}

}
fn main() {}