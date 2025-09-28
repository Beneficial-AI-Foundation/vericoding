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
    /* code modified by LLM (iteration 5): Fixed int usage in executable code */
    let mut result = Vec::new();
    let mut current = start;
    
    if step > 0 {
        // Handle positive step
        while current < stop
            invariant
                step > 0,
                start < stop,
                current >= start,
                current <= stop,
                result@.len() == ((current as int - start as int) / step as int) as nat,
                forall|i: int| 0 <= i < result@.len() ==> result@[i] == start as int + i * step as int,
                current as int == start as int + (result@.len() as int) * step as int,
            decreases (stop as int - current as int)
        {
            result.push(current);
            // Check if we can safely add step
            if current <= i8::MAX - step && current + step <= stop {
                current = current + step;
            } else {
                break;
            }
        }
    } else {
        // Handle negative step
        while current > stop
            invariant
                step < 0,
                start > stop,
                current >= stop,
                current <= start,
                result@.len() == ((start as int - current as int) / (-step as int)) as nat,
                forall|i: int| 0 <= i < result@.len() ==> result@[i] == start as int + i * step as int,
                current as int == start as int + (result@.len() as int) * step as int,
            decreases (current as int - stop as int)
        {
            result.push(current);
            // Check if we can safely add step (which is negative)
            if current >= i8::MIN - step && current + step >= stop {
                current = current + step;
            } else {
                break;
            }
        }
    }
    
    proof {
        assert(result@.len() > 0) by {
            if step > 0 {
                assert(start < stop);
                assert(result@.len() >= 1);
            } else {
                assert(start > stop);
                assert(result@.len() >= 1);
            }
        }
        assert(result@[0] == start as int);
        assert(result@.len() == arange_length(start as int, stop as int, step as int));
    }
    
    result
}
// </vc-code>


}
fn main() {}