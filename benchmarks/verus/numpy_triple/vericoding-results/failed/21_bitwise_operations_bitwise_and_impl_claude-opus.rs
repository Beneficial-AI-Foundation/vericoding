// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] as int >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] as int >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x1[i] as int,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x2[i] as int,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed index in assertions after push */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] as int >= 0,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x1[j] as int,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x2[j] as int,
            forall|j: int| 0 <= j < i ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < i ==> (x1[j] == x2[j] ==> result[j] == x1[j]),
            x1.len() == x2.len(),
        decreases x1.len() - i
    {
        let val = x1[i] & x2[i];
        result.push(val);
        
        assert(result.len() == i + 1);
        assert(result[(result.len() - 1) as int] == val);
        assert(val == (x1[i as int] & x2[i as int]));
        assert(val as int >= 0);
        assert(val as int <= x1[i as int] as int) by {
            // Bitwise AND of two values is at most either value
        }
        assert(val as int <= x2[i as int] as int) by {
            // Bitwise AND of two values is at most either value
        }
        assert((val == 0) <==> (x1[i as int] == 0 || x2[i as int] == 0));
        assert(x1[i as int] == x2[i as int] ==> val == x1[i as int]);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}