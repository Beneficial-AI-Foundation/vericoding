// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_int(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs(a: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == abs_int(a[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): refactored to use while loop with explicit invariants to help verifier prove postconditions */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == abs_int(a[j] as int),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
        decreases a.len() - i
    {
        let x = a[i];
        let abs_val = if x < 0 {
            if x == i8::MIN {
                i8::MAX
            } else {
                -x
            }
        } else {
            x
        };
        result.push(abs_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}