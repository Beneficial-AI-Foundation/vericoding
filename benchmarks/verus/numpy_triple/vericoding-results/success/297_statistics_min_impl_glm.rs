// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        exists|i: int| 0 <= i < a@.len() && a@[i] == result as int,
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implement min using iterative loop */
{
    let mut result = a[0];
    let mut i = 1;
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            exists|j: int| 0 <= j < i && a@[j] == result as int,
            forall|j: int| 0 <= j < i ==> result as int <= a@[j],
        decreases a.len() - i
    {
        if a[i] < result {
            result = a[i];
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}