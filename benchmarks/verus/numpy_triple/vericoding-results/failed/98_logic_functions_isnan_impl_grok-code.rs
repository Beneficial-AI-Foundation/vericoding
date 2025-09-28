// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
    /* code modified by LLM (iteration 5): changed index type to nat, used sequence indexing with @, and fixed assignment with = i + 1 to resolve compilation errors */
    let mut result: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    while i < x@.len()
        invariant
            i <= x@.len(),
            result.len() as nat == i,
            forall|j: nat| 0 <= j < i ==> (result@[j] == (x@[j] != x@[j]))
        decreases x@.len() - i
    {
        result.push(x@[i] != x@[i]);
        i = i + 1;
    }
    result

// </vc-code>

}
fn main() {}