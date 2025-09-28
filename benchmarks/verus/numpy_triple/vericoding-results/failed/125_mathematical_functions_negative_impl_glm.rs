// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): safe negation for i8 that requires input != -128 */
fn safe_negate(x: i8) -> (result: i8)
    requires
        x != -128,
    ensures
        result as int == -(x as int),
{
    -x
}
// </vc-helpers>

// <vc-spec>
fn numpy_negative(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] as int == -(x[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type mismatch in assertion */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= (i as int) <= x.len() as int,
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] as int == -(x[j] as int),
        decreases (x.len() as int) - (i as int)
    {
        assert(x@[i as int] != -128);
        result.push(safe_negate(x[i]));
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}