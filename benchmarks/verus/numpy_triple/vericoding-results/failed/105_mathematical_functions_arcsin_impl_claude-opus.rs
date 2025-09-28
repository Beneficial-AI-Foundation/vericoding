// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -2 <= result[i] as int && result[i] as int <= 2 &&
            (x[i] as int == 0 ==> result[i] as int == 0) &&
            (x[i] as int == 1 ==> result[i] as int == 2) &&
            (x[i] as int == -1 ==> result[i] as int == -2)
        },
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x[i] as int <= x[j] as int ==> result[i] as int <= result[j] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                -2 <= result[j] as int && result[j] as int <= 2 &&
                (x[j] as int == 0 ==> result[j] as int == 0) &&
                (x[j] as int == 1 ==> result[j] as int == 2) &&
                (x[j] as int == -1 ==> result[j] as int == -2)
            },
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i && x[j] as int <= x[k] as int ==> result[j] as int <= result[k] as int,
        decreases x.len() - i
    {
        let val = if x[i] == 0 {
            0i8
        } else if x[i] == 1 {
            2i8
        } else if x[i] == -1 {
            -2i8
        } else {
            x[i]
        };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}