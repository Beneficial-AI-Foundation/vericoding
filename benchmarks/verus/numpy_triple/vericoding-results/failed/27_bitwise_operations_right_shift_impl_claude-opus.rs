// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            i == result.len(),
            n == x1.len(),
            n == x2.len(),
            forall|j: int| 0 <= j < i as int ==> {
                &&& (x1[j] >= 0 ==> result[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> result[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> result[j] == x1[j])
                &&& (x1[j] > 0 ==> result[j] >= 0)
                &&& (x1[j] < 0 ==> result[j] <= 0)
                &&& (x1[j] == 0 ==> result[j] == 0)
            },
            forall|j: int| 0 <= j < n as int ==> x2[j] >= 0,
        decreases n - i
    {
        let val = if x2[i] == 0 {
            x1[i]
        } else if x1[i] >= 0 {
            x1[i] / (1i32 << x2[i])
        } else {
            x1[i] >> x2[i]
        };
        
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}