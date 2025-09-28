// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn greater(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i] as i32 > b[i] as i32)
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] as i32 > b[j] as i32),
            i <= a.len(),
        decreases a.len() - i
    {
        result.push(a[i] as i32 > b[i] as i32);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}