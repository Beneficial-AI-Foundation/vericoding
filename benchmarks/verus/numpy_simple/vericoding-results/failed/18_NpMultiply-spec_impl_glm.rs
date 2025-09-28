// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed indexing and overflow by using int multiplication and adding invariants */
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            a.len() == n,
            b.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] as int == a[j] as int * b[j] as int,
        decreases n - i
    {
        let ai = a[i] as int;
        let bi = b[i] as int;
        let product = ai * bi;
        result.push(product as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}