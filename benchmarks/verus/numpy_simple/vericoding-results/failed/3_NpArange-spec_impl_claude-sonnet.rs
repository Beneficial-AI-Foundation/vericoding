// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_range(start: i8, stop: i8, step: i8) -> bool {
    step != 0 && (if step < 0 { start > stop } else { start < stop })
}

/* helper modified by LLM (iteration 5): Added stronger division properties for proving length bounds */
proof fn arange_length_pos(start: int, stop: int, step: int)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        arange_length(start, stop, step) > 0,
{
    if step < 0 {
        assert(start > stop);
        assert((start - stop) > 0);
        assert((-step) > 0);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(start - stop, -step);
    } else {
        assert(start < stop);
        assert((stop - start) > 0);
        assert(step > 0);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(stop - start, step);
    }
}
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and loop invariants */
    let mut result = Vec::new();
    let mut current = start;
    
    let ghost expected_len = arange_length(start as int, stop as int, step as int);
    
    proof {
        arange_length_pos(start as int, stop as int, step as int);
    }
    
    while (step > 0 && current < stop) || (step < 0 && current > stop)
        invariant
            step != 0,
            if step < 0 { start > stop } else { start < stop },
            result@.len() < expected_len,
            result@.len() == 0 || result@[0] == start as int,
            if step > 0 { current == start + (result@.len() as i8) * step } else { current == start + (result@.len() as i8) * step },
            if step > 0 { current >= start && current < stop } else { current <= start && current > stop },
        decreases
            if step > 0 { (stop - current) as nat } else { (current - stop) as nat },
    {
        result.push(current);
        if step > 0 {
            current = current + step;
        } else {
            current = current + step;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}