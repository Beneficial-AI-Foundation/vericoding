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
    /* code modified by LLM (iteration 4): fixed vec initialization using Vec::new and push to avoid unsupported from_elem */
    let mut result;
    if c1.len() == 0 || c2.len() == 0 {
        result = vec![0i8];
    } else {
        let len = c1.len() + c2.len() - 1;
        result = Vec::new();
        for _ in 0..len {
            result.push(0i8);
        }
        for i in 0..c1.len() {
            for j in 0..c2.len() {
                let idx = i + j;
                let curr = result[idx] as i32;
                let add = (c1[i] as i32) * (c2[j] as i32);
                let newval = (curr + add) as i8;
                result[idx] = newval;
            }
        }
    }
    proof {
        if c1.len() == 0 || c2.len() == 0 {
            assert(result.len() == 1 && result[0] == 0);
        } else {
            assert(result.len() == c1.len() + c2.len() - 1);
        }
        if c2.len() == 1 && c1.len() > 0 {
            assert(forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c1[i] as int * c2[0] as int);
        }
        if c1.len() == 1 && c2.len() > 0 {
            assert(forall|i: int| 0 <= i < c2.len() ==> result[i] as int == c2[i] as int * c1[0] as int);
        }
        if (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0) {
            assert(forall|k: int| 0 <= k < result.len() ==> result[k] == 0);
        }
    }
    result
}
// </vc-code>

}
fn main() {}