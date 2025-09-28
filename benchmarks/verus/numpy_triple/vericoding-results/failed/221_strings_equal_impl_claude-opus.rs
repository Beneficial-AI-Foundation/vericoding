// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): ensure invariants are preserved by asserting them after push */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] == x2@[j]),
            forall|j: int| 0 <= j < i ==> (result@[j] == true <==> x1@[j] == x2@[j]),
        decreases x1.len() - i
    {
        let eq = x1[i] == x2[i];
        result.push(eq);
        proof {
            assert(result.len() == i + 1);
            assert(result@[i as int] == eq);
            assert(result@[i as int] == (x1@[i as int] == x2@[i as int]));
            assert(forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] == x2@[j]));
            assert(forall|j: int| 0 <= j < i + 1 ==> result@[j] == (x1@[j] == x2@[j]));
            assert(forall|j: int| 0 <= j < i + 1 ==> (result@[j] == true <==> x1@[j] == x2@[j]));
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}