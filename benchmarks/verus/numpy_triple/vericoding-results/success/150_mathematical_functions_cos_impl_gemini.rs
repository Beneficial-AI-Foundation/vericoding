// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_cos(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -1 <= result@[i] as int <= 1 &&
            (x@[i] as int == 0 ==> result@[i] as int == 1)
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                -1 <= result@[j] as int <= 1 &&
                (x@[j] as int == 0 ==> result@[j] as int == 1)
            }
        decreases x.len() - i
    {
        let val = x[i];
        if val == 0 {
            result.push(1);
        } else {
            result.push(0);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}