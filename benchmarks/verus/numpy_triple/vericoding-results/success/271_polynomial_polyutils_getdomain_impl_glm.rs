// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): named the return value in function signature */
fn find_min_max(x: Vec<i8>) -> (result: (i8, i8))
    requires x@.len() > 0,
    ensures
        result.0 as int <= result.1 as int,
        forall|i: int| 0 <= i < x@.len() ==> (result.0 as int) <= (x@[i] as int) && (x@[i] as int) <= (result.1 as int),
        exists|i: int| 0 <= i < x@.len() && (x@[i] as int) == (result.0 as int),
        exists|j: int| 0 <= j < x@.len() && (x@[j] as int) == (result.1 as int),
{
    let mut min = x[0];
    let mut max = x[0];
    let mut i: usize = 1;
    while i < x.len()
        invariant
            1 <= i <= x@.len(),
            forall|j: int| 0 <= j < i ==> min as int <= x@[j] as int && x@[j] as int <= max as int,
            exists|j: int| 0 <= j < i && x@[j] as int == min as int,
            exists|j: int| 0 <= j < i && x@[j] as int == max as int,
        decreases x@.len() - i
    {
        if x[i] < min {
            min = x[i];
        } else if x[i] > max {
            max = x[i];
        }
        i += 1;
    }
    (min, max)
}
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
    /* code modified by LLM (iteration 5): no changes needed, helper call remains valid */
    let (min_val, max_val) = find_min_max(x);
    vec![min_val, max_val]
}
// </vc-code>


}
fn main() {}