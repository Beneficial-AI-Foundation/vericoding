// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parameter types to accept i32 instead of int */
spec fn pow2(n: int) -> int
    requires n >= 0
{
    if n == 0 { 1 } else { 2 * pow2(n - 1) }
}

proof fn pow2_shift_equiv(n: int)
    requires n >= 0
    ensures pow2(n) == 1i32 << (n as i32)
{
    if n == 0 {
    } else {
        pow2_shift_equiv(n - 1);
    }
}

proof fn div_shift_equiv(x: int, n: int)
    requires x >= 0, n >= 0
    ensures x / (1i32 << (n as i32)) == x >> (n as i32)
{
    pow2_shift_equiv(n);
}
// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches by using int for div_shift_equiv call */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < result.len() ==> {
                &&& (x1[j] >= 0 ==> result[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> result[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> result[j] == x1[j])
                &&& (x1[j] > 0 ==> result[j] >= 0)
                &&& (x1[j] < 0 ==> result[j] <= 0)
                &&& (x1[j] == 0 ==> result[j] == 0)
            },
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0
    {
        let val = if x1[i] >= 0 {
            proof {
                div_shift_equiv(x1[i] as int, x2[i] as int);
            }
            x1[i] / (1i32 << x2[i])
        } else {
            x1[i] >> x2[i]
        };
        
        result.push(val);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}