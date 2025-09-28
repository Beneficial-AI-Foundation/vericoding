// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotation in quantifier */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < max_len
        invariant
            0 <= i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if j < c1@.len() { c1@[j] as int } else { 0 };
                let coeff2 = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == coeff1 + coeff2
            },
        decreases max_len - i
    {
        let coeff1: i8 = if i < c1.len() { c1[i] } else { 0 };
        let coeff2: i8 = if i < c2.len() { c2[i] } else { 0 };
        
        // Check for overflow before adding
        assert(coeff1 as int + coeff2 as int >= -128);
        assert(coeff1 as int + coeff2 as int <= 127);
        
        let sum: i8 = coeff1 + coeff2;
        result.push(sum);
        
        proof {
            assert(result.len() == i + 1);
            assert(result@[i as int] == sum);
            assert(forall|j: int| 0 <= j < i + 1 ==> {
                let c1_val = if j < c1@.len() { c1@[j] as int } else { 0 };
                let c2_val = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == if j < i {
                    c1_val + c2_val
                } else {
                    sum as int
                }
            });
            assert(sum as int == (if i < c1@.len() { c1@[i as int] as int } else { 0 }) + (if i < c2@.len() { c2@[i as int] as int } else { 0 }));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}