// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        let elem = a[i];
        result.push(elem);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}