// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ix_(seq1: Vec<i8>, seq2: Vec<i8>) -> (result: (Vec<Vec<i8>>, Vec<Vec<i8>>))
    requires 
        seq1.len() > 0,
        seq2.len() > 0,
    ensures 

        result.0.len() == seq1.len(),
        forall|i: int| 0 <= i < seq1@.len() ==> result.0@[i].len() == 1,
        forall|i: int| 0 <= i < seq1@.len() ==> result.0@[i][0] == seq1@[i],

        result.1.len() == 1,
        result.1@[0].len() == seq2.len(),
        forall|j: int| 0 <= j < seq2@.len() ==> result.1@[0][j] == seq2@[j],

        forall|i: int, j: int| 0 <= i < seq1@.len() && 0 <= j < seq2@.len() ==> 
            result.0@[i][0] == seq1@[i] && result.1@[0][j] == seq2@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to while loops */
    let mut result_0: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    while i < seq1.len()
        invariant
            i <= seq1.len(),
            result_0.len() == i,
            forall|k: int| 0 <= k < i ==> result_0@[k].len() == 1,
            forall|k: int| 0 <= k < i ==> result_0@[k][0] == seq1@[k],
        decreases seq1.len() - i
    {
        let mut inner_vec = Vec::new();
        inner_vec.push(seq1[i]);
        result_0.push(inner_vec);
        i += 1;
    }
    
    let mut result_1: Vec<Vec<i8>> = Vec::new();
    let mut outer_vec = Vec::new();
    let mut j = 0;
    while j < seq2.len()
        invariant
            j <= seq2.len(),
            outer_vec.len() == j,
            forall|k: int| 0 <= k < j ==> outer_vec@[k] == seq2@[k],
        decreases seq2.len() - j
    {
        outer_vec.push(seq2[j]);
        j += 1;
    }
    result_1.push(outer_vec);
    
    (result_0, result_1)
}
// </vc-code>

}
fn main() {}