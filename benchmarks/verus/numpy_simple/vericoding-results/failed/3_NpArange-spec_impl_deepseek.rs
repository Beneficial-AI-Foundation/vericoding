// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


spec fn arange_length_step_neg(start: int, stop: int, step: int) -> bool {
    step < 0 && start > stop
}

spec fn arange_length_step_pos(start: int, stop: int, step: int) -> bool {
    step > 0 && start < stop
}

proof fn arange_length_nonnegative_lemma(start: int, stop: int, step: int)
    ensures
        arange_length(start, stop, step) >= 0
{
}

proof fn arange_single_element_lemma(start: int, stop: int, step: int)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        arange_length(start, stop, step) >= 1
{
}

/* helper modified by LLM (iteration 5): Fixed safe conversion to use proper i8 casting */
fn safe_int_to_i8(x: int) -> (result: i8)
    requires
        x >= -128 && x <= 127
    ensures
        result as int == x
{
    if x >= 0 {
        (x as u8) as i8
    } else {
        (-((-x) as u8)) as i8
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
/* code modified by LLM (iteration 5): Fixed integer arithmetic using safe conversion helper */
{
    let mut result: Vec<i8> = Vec::new();
    let mut current = start;
    let step_i8 = step;
    
    while 
        if step_i8 < 0 {
            current > stop
        } else {
            current < stop
        }
        invariant
            result@.len() == arange_length(start as int, current as int, step_i8 as int),
            result@.len() <= arange_length(start as int, stop as int, step_i8 as int),
            if result@.len() > 0 { result@[0] == start as int } else { true }
        decreases 
            if step_i8 < 0 {
                (current as int - stop as int) as nat
            } else {
                (stop as int - current as int) as nat
            }
    {
        result.push(current);
        let next_val = current as i16 + step_i8 as i16;
        current = safe_int_to_i8(next_val as int);
    }
    
    result
}
// </vc-code>


}
fn main() {}