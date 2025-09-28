// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn getdomain(x: Vec<i8>) -> (result: Vec<i8>)
    requires x@.len() > 0,
    ensures
        result@.len() == 2,
        result@[0] as int <= result@[1] as int,
        forall|i: int| 0 <= i < x@.len() ==> result@[0] as int <= x@[i] as int && x@[i] as int <= result@[1] as int,
        exists|i: int| 0 <= i < x@.len() && x@[i] as int == result@[0] as int,
        exists|j: int| 0 <= j < x@.len() && x@[j] as int == result@[1] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix verification error */
    let mut min = x[0];
    let mut max = x[0];
    let mut i = 1;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            forall|j: int| 0 <= j < i ==> min as int <= x@[j] as int && x@[j] as int <= max as int,
            exists|j: int| 0 <= j < i && x@[j] as int == min as int,
            exists|j: int| 0 <= j < i && x@[j] as int == max as int,
            min as int <= max as int,
        decreases x.len() - i
    {
        if x[i] < min {
            min = x[i];
        }
        if x[i] > max {
            max = x[i];
        }
        i = i + 1;
    }
    
    let result = vec![min, max];
    result
}
// </vc-code>


}
fn main() {}