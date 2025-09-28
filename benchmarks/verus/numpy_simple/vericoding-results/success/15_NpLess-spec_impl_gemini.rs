// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn less(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (a@[i] < b@[i])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] < b@[j]),
        decreases a.len() - i
    {
        let cmp = a[i] < b[i];
        result.push(cmp);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}