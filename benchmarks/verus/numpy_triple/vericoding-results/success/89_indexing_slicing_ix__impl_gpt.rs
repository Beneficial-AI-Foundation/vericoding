// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn singleton_vec_i8(x: i8) -> (result: Vec<i8>)
    ensures
        result.len() == 1,
        result@[0] == x,
{
    let mut v: Vec<i8> = Vec::new();
    v.push(x);
    v
}

/* helper modified by LLM (iteration 2): use usize loop index and proper spec conversions */
fn copy_vec_i8(src: &Vec<i8>) -> (dest: Vec<i8>)
    ensures
        dest.len() == src.len(),
        forall|k: int| 0 <= k && k < src@.len() ==> dest@[k] == src@[k],
{
    let mut d: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < src.len()
        invariant
            j as int <= src@.len(),
            d.len() == j,
            forall|k: int| 0 <= k && k < j as int ==> d@[k] == src@[k],
        decreases src@.len() - j as int
    {
        let val = src[j];
        d.push(val);
        j += 1;
    }
    d
}
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
    /* code modified by LLM (iteration 2): use usize indices and maintain invariants relating views */
    let mut rows0: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < seq1.len()
        invariant
            i as int <= seq1@.len(),
            rows0.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> rows0@[k].len() == 1,
            forall|k: int| 0 <= k && k < i as int ==> rows0@[k][0] == seq1@[k],
        decreases seq1@.len() - i as int
    {
        let val = seq1[i];
        let single = singleton_vec_i8(val);
        rows0.push(single);
        i += 1;
    }

    let row = copy_vec_i8(&seq2);
    let mut rows1: Vec<Vec<i8>> = Vec::new();
    rows1.push(row);

    (rows0, rows1)
}
// </vc-code>

}
fn main() {}