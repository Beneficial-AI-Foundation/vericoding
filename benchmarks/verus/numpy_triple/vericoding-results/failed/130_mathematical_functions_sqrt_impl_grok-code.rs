// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sqrt_single(val: i8) -> (result: i8)

    requires val >= 0,
    ensures
        result >= 0,
        (result as int) * (result as int) <= (val as int),
        ((result as int) + 1) * ((result as int) + 1) > (val as int),
{
/* helper modified by LLM (iteration 5): Set high to 11 to prevent overflows and ensure invariants hold without arithmetic issues. */
    let mut low: i8 = 0;
    let mut high: i8 = 11;
    while low < high
        invariant
            0 <= low <= high,
            low as int * low as int <= val as int,
            (high as int + 1) * (high as int + 1) > val as int,
        decreases high - low
    {
        let mid: i8 = (((low as i16 + high as i16 + 1) / 2) as i8);
        if (mid as i16) * (mid as i16) <= (val as i16) {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    low
}
// </vc-helpers>

// <vc-spec>
fn sqrt(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (x@[i] >= 0 ==> result@[i] * result@[i] == x@[i] && result@[i] >= 0)
            &&& (x@[i] == 0 ==> result@[i] == 0)
            &&& (x@[i] == 1 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added invariant for length storage to aid verification, ensuring index bounds are properly checked against original vector length. */
    let mut result: Vec<i8> = Vec::new();
    let length: usize = x.len();
    let mut index: usize = 0;
    while index < length
        invariant
            result@.len() == index,
            length as int == x@.len(),
            forall|i: int| 0 <= i < index ==> {
                &&& if x@[i] >= 0 {
                    (result@[i] as int) * (result@[i] as int) <= (x@[i] as int) &&
                    ((result@[i] as int) + 1) * ((result@[i] as int) + 1) > (x@[i] as int) &&
                    result@[i] >= 0
                } else {
                    true
                }
                &&& (x@[i] == 0 ==> result@[i] == 0)
                &&& (x@[i] == 1 ==> result@[i] == 1)
            },
        decreases length - index
    {
        let val = x[index];
        let sqrt_val = if val >= 0 { sqrt_single(val) } else { 0 };
        result.push(sqrt_val);
        index = index + 1;
    }
    result
}
// </vc-code>


}
fn main() {}