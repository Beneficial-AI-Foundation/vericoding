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
/* code modified by LLM (iteration 4): added parentheses in invariant comparisons to fix compilation error */
{
    let mut min: i8 = x[0];
    let mut max: i8 = x[0];
    let mut min_idx: usize = 0;
    let mut max_idx: usize = 0;
    let mut idx: usize = 1;
    while idx < x.len()
        invariant
            0 < (idx as int) <= x@.len(),
            0 <= (min_idx as int) < (idx as int),
            0 <= (max_idx as int) < (idx as int),
            (min as int) <= (max as int),
            forall|j: int| 0 <= j < (idx as int) ==> (min as int) <= x@[j] as int,
            forall|j: int| 0 <= j < (idx as int) ==> x@[j] as int <= (max as int),
            x@[(min_idx as int)] as int == (min as int),
            x@[(max_idx as int)] as int == (max as int),
        decreases x@.len() - (idx as int)
    {
        if x[idx] < min {
            min = x[idx];
            min_idx = idx;
        } else if x[idx] > max {
            max = x[idx];
            max_idx = idx;
        }
        idx += 1;
    }
    let result = vec![min, max];
    result
}
// </vc-code>


}
fn main() {}