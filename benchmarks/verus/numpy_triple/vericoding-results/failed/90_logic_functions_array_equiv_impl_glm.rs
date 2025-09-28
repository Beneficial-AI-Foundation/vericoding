// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added invariant that n equals vector lengths to fix indexing and postcondition */
{
    let mut i = 0;
    let n = a1.len();
    while i < n
        invariant
            n == a1@.len(),
            n == a2@.len(),
            0 <= i <= n,
            (forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j])
        decreases n - i
    {
        if a1[i] != a2[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}