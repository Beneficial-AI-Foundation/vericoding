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
    /* code modified by LLM (iteration 5): ensure i < b.len() before accessing b[i] by using a.len() == b.len() precondition */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] as i32 > b[j] as i32)
        decreases a.len() - i
    {
        let comparison = a[i as usize] as i32 > b[i as usize] as i32;
        result.push(comparison);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}