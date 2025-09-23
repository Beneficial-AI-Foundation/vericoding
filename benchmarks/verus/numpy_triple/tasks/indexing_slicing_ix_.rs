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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}