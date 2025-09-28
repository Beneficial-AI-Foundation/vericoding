// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn greater_equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i] as int >= b[i] as int)
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] as int >= b[j] as int),
        decreases a.len() - i
    {
        let ge = a[i] >= b[i];
        result.push(ge);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}