// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_greater(x1: &Vec<i8>, x2: &Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == (x1[i] as int > x2[i] as int)) &&
            (result[i] == true ==> !(x2[i] as int > x1[i] as int)) &&
            (result[i] == true || result[i] == false)
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x1@[j] > x2@[j]),
        decreases x1.len() - i
    {
        result.push(x1[i] > x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}