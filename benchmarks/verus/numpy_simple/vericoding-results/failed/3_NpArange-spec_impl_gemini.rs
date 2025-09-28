// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [added proof body to lemma] */
proof fn lemma_arange_val_in_i8_bounds(start: int, stop: int, step: int, i: int)
    requires
        -128 <= start <= 127,
        -128 <= stop <= 127,
        step != 0,
        if step > 0 { start < stop } else { start > stop },
        0 <= i <= arange_length(start, stop, step),
    ensures
        -128 <= start + i * step <= 127,
{
    let len = arange_length(start, stop, step);
    if step > 0 {
        assert(start < stop);
        assert(i <= (stop - start) / step);
        assert(i * step <= stop - start) by(nonlinear_arith)
            requires
                i >= 0,
                step > 0,
                stop - start >= 0,
                i <= (stop - start) / step, 
        { };

        assert(start + i * step <= stop);
        assert(start + i * step <= 127);
        assert(i * step >= 0);
        assert(start + i * step >= start);
        assert(start + i * step >= -128);
    } else {
        let neg_step = -step;
        assert(start > stop);
        assert(i <= (start - stop) / neg_step);
        assert(i * neg_step <= start - stop) by(nonlinear_arith)
            requires
                i >= 0,
                neg_step > 0,
                start - stop >= 0,
                i <= (start - stop) / neg_step,
        { };

        assert(i * (-step) <= start - stop);
        assert(-(i * step) <= start - stop);
        assert(stop - start <= i * step);
        assert(stop <= start + i * step);
        assert(-128 <= start + i * step);
        assert(i * step <= 0);
        assert(start + i * step <= start);
        assert(start + i * step <= 127);
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
    /* code modified by LLM (iteration 5): [use ghost vars for specs and wider types to prevent overflow] */
    ghost let start_int = start as int;
    ghost let stop_int = stop as int;
    ghost let step_int = step as int;

    // Use executable types for length calculation to avoid ghost type errors.
    let start_w = start as i32;
    let stop_w = stop as i32;
    let step_w = step as i32;

    let len_val = if step > 0 {
        (stop_w - start_w) / step_w
    } else { // step < 0 because requires says step != 0
        (start_w - stop_w) / (-step_w)
    };

    proof {
        assert(len_val >= 0);
        assert(len_val < usize::MAX as i32);
    }
    let len = len_val as usize;
    
    ghost let spec_len = arange_length(start_int, stop_int, step_int);
    assert(len as nat == spec_len) by(nonlinear_arith) {
        if step > 0 {
            assert(((stop_w - start_w) / step_w) as int == (stop_int - start_int) / step_int);
        } else {
            assert(((start_w - stop_w) / (-step_w)) as int == (start_int - stop_int) / (-step_int));
        }
    };
    
    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;
    
    // Using a wider type for `current` prevents overflow on `current + step`
    let mut current_val = start as i32;

    while i < len
        invariant
            i <= len,
            result.len() == i,
            len as nat == spec_len,
            -128 <= current_val <= 127,
            current_val as int == start_int + (i as int) * step_int,
            forall|j: int| 0 <= j < i as int ==> result@[j] as int == start_int + j * step_int,
        decreases len - i
    {
        proof {
            lemma_arange_val_in_i8_bounds(start_int, stop_int, step_int, i as int);
        }

        result.push(current_val as i8);
        
        current_val = current_val + step_w;
        i = i + 1;
        
        proof {
            if i < len {
                lemma_arange_val_in_i8_bounds(start_int, stop_int, step_int, i as int);
            }
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}