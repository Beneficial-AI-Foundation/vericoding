// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>

    /* code modified by LLM (iteration 2): Implemented addition with while loop, invariant, decreases, and exec to handle overflow */
    let mut result: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < a@.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j as nat] as int == a@[j as nat] as int + b@[j as nat] as int
        decreases a@.len() - i
    {
        let sum = exec(a@[i as nat] + b@[i as nat]);
        result.push(sum);
        i += 1;
    }
    result

// </vc-code>


}
fn main() {}