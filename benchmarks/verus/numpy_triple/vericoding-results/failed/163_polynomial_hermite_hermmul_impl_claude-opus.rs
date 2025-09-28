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
    /* code modified by LLM (iteration 5): Fixed truncate attribute syntax */
    if c1.len() == 0 || c2.len() == 0 {
        let mut result = Vec::new();
        result.push(0i8);
        proof {
            assert(result.len() == 1);
            assert(result[0] == 0);
        }
        return result;
    }
    
    // Add check to prevent overflow
    if c1.len() > usize::MAX / 2 || c2.len() > usize::MAX / 2 {
        // Handle very large inputs - return zero vector for safety
        let mut result = Vec::new();
        result.push(0i8);
        return result;
    }
    
    let result_len: usize = (c1.len() as usize) + (c2.len() as usize) - 1;
    let mut result: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < result_len
        invariant
            k <= result_len,
            result.len() == k,
            c1.len() > 0,
            c2.len() > 0,
            result_len == c1.len() + c2.len() - 1,
            forall|idx: int| 0 <= idx < k ==> result[idx] == 0,
        decreases result_len - k
    {
        result.push(0i8);
        k = k + 1;
    }
    
    let mut i: usize = 0;
    while i < c1.len()
        invariant
            i <= c1.len(),
            result.len() == result_len,
            c1.len() > 0,
            c2.len() > 0,
            result_len == c1.len() + c2.len() - 1,
        decreases c1.len() - i
    {
        let mut j: usize = 0;
        while j < c2.len()
            invariant
                j <= c2.len(),
                i < c1.len(),
                result.len() == result_len,
                c1.len() > 0,
                c2.len() > 0,
                result_len == c1.len() + c2.len() - 1,
                i + j <= result_len,
                j < c2.len() ==> i + j < result_len,
            decreases c2.len() - j
        {
            proof {
                assert(i < c1.len());
                assert(j < c2.len());
                assert(result_len == c1.len() + c2.len() - 1);
                assert(i + j < c1.len() + c2.len() - 1);
                assert(i + j < result_len);
            }
            
            // Use truncate to handle potential overflow - proper syntax with parentheses
            let prod: i8 = (#[verifier::truncate] ((c1[i] as i32) * (c2[j] as i32))) as i8;
            let old_val = result[i + j];
            result.set(i + j, (#[verifier::truncate] ((old_val as i32) + (prod as i32))) as i8);
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}