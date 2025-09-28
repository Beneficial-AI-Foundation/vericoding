// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c1[i] as int * c2[0] as int,
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] as int == c2[i] as int * c1[0] as int,

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    if c1.is_empty() || c2.is_empty() {
        return vec![0];
    }

    if c2.len() == 1 {
        let scalar = c2[0];
        let mut res = Vec::with_capacity(c1.len());
        for i in 0..c1.len() {
            res.push(c1[i] * scalar);
        }
        return res;
    }

    if c1.len() == 1 {
        let scalar = c1[0];
        let mut res = Vec::with_capacity(c2.len());
        for i in 0..c2.len() {
            res.push(c2[i] * scalar);
        }
        return res;
    }

    let m = c1.len();
    let n = c2.len();
    let mut result = vec![0; m + n - 1];
    for i in 0..m {
        for j in 0..n {
            let k = i + j;
            result[k] += c1[i] * c2[j];
        }
    }
    result
}
// </vc-code>

}
fn main() {}