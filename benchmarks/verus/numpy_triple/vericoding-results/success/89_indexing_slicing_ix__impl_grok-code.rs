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
    let mut result0 = Vec::<Vec<i8>>::new();
    let mut i = 0;
    while i < seq1.len()
        invariant
            i >= 0,
            i <= seq1@.len(),
            result0.len() as int == i,
            forall|k: int| 0 <= k < i ==> result0@[k]@.len() == 1,
            forall|k: int| 0 <= k < i ==> result0@[k]@[0] == seq1@[k],
        decreases seq1@.len() - i
    {
        let mut inner = Vec::<i8>::new();
        inner.push(seq1[i]);
        result0.push(inner);
        i = i + 1;
    }
    let mut result1 = Vec::<Vec<i8>>::new();
    result1.push(seq2);
    (result0, result1)
}
// </vc-code>

}
fn main() {}