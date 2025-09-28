// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed indexing type errors by using i as int */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] as int == x1[j] as int + x2[j] as int,
        decreases n - i
    {
        // Check for overflow before adding
        assert(x1[i as int] as int + x2[i as int] as int >= -128);
        assert(x1[i as int] as int + x2[i as int] as int <= 127);
        
        let sum = x1[i] + x2[i];
        result.push(sum);
        
        proof {
            assert(result.len() == i + 1);
            assert(result[i as int] == sum);
            assert(forall|j: int| 0 <= j < i ==> result[j] as int == x1[j] as int + x2[j] as int);
            assert(result[i as int] as int == x1[i as int] as int + x2[i as int] as int);
            assert(forall|j: int| 0 <= j < i + 1 ==> result[j] as int == x1[j] as int + x2[j] as int);
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}