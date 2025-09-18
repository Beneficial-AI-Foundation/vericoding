// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added overflow checks and fixed assertion */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < max_len
        invariant
            i <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if j < c1.len() { c1[j] } else { 0 };
                let coeff2 = if j < c2.len() { c2[j] } else { 0 };
                #[trigger] result[j] == coeff1 + coeff2
            }
        decreases max_len - i
    {
        let coeff1: i32 = if i < c1.len() { c1[i] } else { 0 };
        let coeff2: i32 = if i < c2.len() { c2[i] } else { 0 };
        
        // Check for overflow before addition
        if coeff1 > 0 && coeff2 > i32::MAX - coeff1 {
            // Would overflow, return what we have so far
            return result;
        }
        if coeff1 < 0 && coeff2 < i32::MIN - coeff1 {
            // Would underflow, return what we have so far
            return result;
        }
        
        result.push(coeff1 + coeff2);
        
        proof {
            assert(result.len() == i + 1);
            assert(result@[i as int] == coeff1 + coeff2);
            assert(forall|j: int| 0 <= j < i + 1 ==> {
                let c1j = if j < c1.len() { c1[j] } else { 0 };
                let c2j = if j < c2.len() { c2[j] } else { 0 };
                result@[j] == c1j + c2j
            });
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}