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
{
    /* code modified by LLM (iteration 5): fixed invariant to use a.len() == b.len() precondition and added overflow check */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == a[j] as int + b[j] as int,
        decreases a.len() - i
    {
        let sum = a[i] as i32 + b[i] as i32;
        assert(-128 <= sum <= 127);
        result.push(sum as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}