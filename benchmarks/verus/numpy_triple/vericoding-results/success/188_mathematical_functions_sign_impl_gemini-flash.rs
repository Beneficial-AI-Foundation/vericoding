// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sign(x: Vec<i8>) -> (result: Vec<i8>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            (x@[i] < 0 ==> result@[i] == -1) &&
            (x@[i] == 0 ==> result@[i] == 0) &&
            (x@[i] > 0 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (x@[j] < 0 ==> result@[j] == -1) &&
                (x@[j] == 0 ==> result@[j] == 0) &&
                (x@[j] > 0 ==> result@[j] == 1)
            },
            i <= x.len(),
        decreases x.len() - i
    {
        if x[i] < 0 {
            result.push(-1);
        } else if x[i] == 0 {
            result.push(0);
        } else {
            result.push(1);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}