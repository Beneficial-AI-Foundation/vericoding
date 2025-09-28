// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn zeros_like(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0,
        forall|v: &Vec<i32>| v.len() == result.len() ==> {
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] + v[i] == v[i] && v[i] + result[i] == v[i]
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 0,
        decreases a.len() - i,
    {
        result.push(0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}