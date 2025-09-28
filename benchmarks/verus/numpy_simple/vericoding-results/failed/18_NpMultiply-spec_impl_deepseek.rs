// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed spec_index_valid to use vector length */
#[verifier::spec]
fn spec_mult(i: int, j: int) -> int {
    i * j
}

#[verifier::spec]
fn spec_index_valid<T>(v: &Vec<T>, i: int) -> bool {
    0 <= i < v.len()
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed bounds checking with vector references */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let n = a.len();
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> result@[k] as int == spec_mult(a@[k] as int, b@[k] as int)
        decreases n - i
    {
        assert(spec_index_valid(&a, i as int));
        assert(spec_index_valid(&b, i as int));
        let product = a[i] * b[i];
        result.push(product);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}