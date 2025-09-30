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
    /* code modified by LLM (iteration 4): fixed bounds check and invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> (0 <= j < b.len() && result[j] == (a[j] as int >= b[j] as int)),
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());
        let comparison = a[i as usize] >= b[i as usize];
        result.push(comparison);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}