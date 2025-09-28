// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn arange_length(start: int, stop: int, step: int) -> nat
{
    if step != 0 {
        if step < 0 {
            if start > stop {
                ((start - stop) / (-step)) as nat
            } else {
                0
            }
        } else {
            if start < stop {
                ((stop - start) / step) as nat
            } else {
                0
            }
        }
    } else {
        0
    }
}

fn arange(start: i8, stop: i8, step: i8) -> (result: Vec<i8>)
    requires 
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        result@.len() == arange_length(start as int, stop as int, step as int),
        result@.len() > 0,
        result@[0] == start as int
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed overflow by using i32 for calculations internally */
let mut current: i32 = start as i32;
let mut result = Vec::new();
result.push(start);
let stop_i32 = stop as i32;
let step_i32 = step as i32;
while ((step_i32 > 0 && current + step_i32 < stop_i32) || (step_i32 < 0 && current + step_i32 > stop_i32))
    invariant
        result@.len() >= 1,
        result@[0] == start as int,
        forall |k: int| 0 <= k < result@.len() ==> result@[k] == start as int + k * (step as int)
    decreases if step_i32 > 0 { (stop_i32 - current) as nat } else { (current - stop_i32) as nat }
{
    current = current + step_i32;
    result.push(current as i8);
}
assert(result@.len() == arange_length(start as int, stop as int, step as int));
result
}
// </vc-code>


}
fn main() {}