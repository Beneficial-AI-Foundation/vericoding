// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_non_zero_vector(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn floor_divide(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        is_non_zero_vector(a@.map(|i, x: i8| x as i32)),
        is_non_zero_vector(b@.map(|i, x: i8| x as i32)),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == (a[i] as i32) / (b[i] as i32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added bounds checks and range assertions */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as i32 == (a@[j] as i32) / (b@[j] as i32),
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(i < b.len());
        let quotient = (a[i] as i32) / (b[i] as i32);
        assert(-128 <= quotient <= 127);
        result.push(quotient as i8);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}