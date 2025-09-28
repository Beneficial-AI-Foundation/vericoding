// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<Vec<i8>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] as int == a[i] as int * b[j] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and overflow issues */
    let mut result: Vec<Vec<i8>> = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result@[k].len() == b.len(),
            forall|k: int, j: int| 0 <= k < result.len() && 0 <= j < result@[k].len() ==> 
                result@[k]@[j] as int == a@[k] as int * b@[j] as int,
    {
        let mut row: Vec<i8> = Vec::new();
        
        for j in 0..b.len()
            invariant
                row.len() == j,
                forall|l: int| 0 <= l < row.len() ==> 
                    row@[l] as int == a@[i] as int * b@[l] as int,
        {
            proof {
                assert(i < a.len());
                assert(j < b.len());
                assert(0 <= i < a@.len());
                assert(0 <= j < b@.len());
            }
            let product = (a[i] as i32) * (b[j] as i32);
            row.push(#[verifier::truncate] product as i8);
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}