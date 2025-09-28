// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed spec functions to use proper f32 arithmetic operators */
spec fn spec_mul_f32(a: f32, b: f32) -> f32 {
    a * b
}

spec fn spec_add_f32(a: f32, b: f32) -> f32 {
    a + b
}

spec fn spec_sub_f32(a: f32, b: f32) -> f32 {
    a - b
}

proof fn chebpoly0(val: f32) -> (result: f32)
    ensures result == 1.0f32
{
    1.0f32
}

proof fn chebpoly1(val: f32) -> (result: f32)
    ensures result == val
{
    val
}

proof fn chebpoly_next(n: nat, x: f32, prev: f32, prev_prev: f32) -> (result: f32)
    requires n >= 2
    ensures result == spec_sub_f32(spec_mul_f32(spec_mul_f32(2.0f32, x), prev), prev_prev)
{
    spec_sub_f32(spec_mul_f32(spec_mul_f32(2.0f32, x), prev), prev_prev)
}
// </vc-helpers>

// <vc-spec>
fn chebvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires deg >= 0,
    ensures

        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg + 1),
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0f32,

        deg >= 1 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed indexing issues and proper sequence access using @ operator */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let n = x.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (deg + 1),
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0f32,
            deg >= 1 ==> forall|j: int| 0 <= j < i ==> result[j][1] == x@[j as int]
    {
        let mut row: Vec<f32> = Vec::new();
        row.push(1.0f32);
        
        if deg >= 1 {
            row.push(x@[i as int]);
            
            let mut k: usize = 2;
            while k <= deg
                invariant
                    2 <= k <= deg + 1,
                    row.len() == k,
                    forall|l: int| 0 <= l < k ==> row[l] == spec_sub_f32(spec_mul_f32(spec_mul_f32(2.0f32, x@[i as int]), (if l >= 1 { row[l - 1] } else { 0.0 })), (if l >= 2 { row[l - 2] } else { 0.0 }))
            {
                let prev = row[k - 1];
                let prev_prev = row[k - 2];
                let next_val = spec_sub_f32(spec_mul_f32(spec_mul_f32(2.0f32, x@[i as int]), prev), prev_prev);
                row.push(next_val);
                k += 1;
            }
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}