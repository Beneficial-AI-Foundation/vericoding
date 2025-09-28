// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper for checking shift amount bounds */
fn is_valid_shift(shift: i32) -> (res: bool)
    ensures res == (0 <= shift < 32)
{
    0 <= shift && shift < 32
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
{
    /* code modified by LLM (iteration 5): fixed bounds checking and array access */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x1@[j] >= 0 ==> result@[j] == x1@[j] / (1i32 << x2@[j]))
                &&& (x1@[j] < 0 ==> result@[j] == x1@[j] >> x2@[j])
                &&& (x2@[j] == 0 ==> result@[j] == x1@[j])
                &&& (x1@[j] > 0 ==> result@[j] >= 0)
                &&& (x1@[j] < 0 ==> result@[j] <= 0)
                &&& (x1@[j] == 0 ==> result@[j] == 0)
            },
        decreases x1.len() - i
    {
        let shift_amount = x2[i];
        let value = x1[i];
        
        proof {
            assert(0 <= i < x2.len());
            assert(shift_amount >= 0);
            assert(shift_amount < 32);
        }
        
        let shifted_value = if value >= 0 {
            if shift_amount < 32 {
                value / (1i32 << shift_amount)
            } else {
                0
            }
        } else {
            value >> shift_amount
        };
        
        result.push(shifted_value);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}