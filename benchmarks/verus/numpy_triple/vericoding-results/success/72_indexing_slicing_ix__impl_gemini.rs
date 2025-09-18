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
    /* code modified by LLM (iteration 3): added decreases clause to fix termination error */
    let mut res0: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < seq1.len()
        invariant
            0 <= i <= seq1.len(),
            res0.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] res0@[k].len() == 1,
            forall|k: int| 0 <= k < i ==> #[trigger] res0@[k][0] == seq1@[k],
        decreases seq1.len() - i,
    {
        let item = seq1[i];
        let inner_vec = vec![item];
        res0.push(inner_vec);
        i = i + 1;
    }

    let res1 = vec![seq2];

    (res0, res1)
}
// </vc-code>

}
fn main() {}