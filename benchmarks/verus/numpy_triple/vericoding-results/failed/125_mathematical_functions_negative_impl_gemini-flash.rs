// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn negative_i8_spec(val: i8) -> (result: i8)
    ensures
        result as int == -(val as int)
{
    -val
}
// </vc-helpers>

// <vc-spec>
fn numpy_negative(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] as int == -(x[i] as int)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.reserve(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == -(x[j] as int)
        decreases x.len() - i
    {
        let val_at_i = x[i];
        let neg_val_at_i = negative_i8_spec(val_at_i);
        result.push(neg_val_at_i);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}