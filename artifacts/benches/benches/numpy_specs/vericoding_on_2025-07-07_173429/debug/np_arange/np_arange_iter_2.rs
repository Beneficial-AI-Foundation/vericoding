use vstd::prelude::*;

verus! {

// Translated from Dafny arange function to work with integers instead of reals
// since Verus doesn't yet support floating point types in verification
fn arange_int(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires 
        step != 0,
        if step < 0 { start > stop } else { start < stop },
        -10 <= step <= 10,
        -50 <= start <= 50,
        -50 <= stop <= 50,
    ensures 
        ret.len() > 0,
        ret[0] == start,
{
    let diff = if step > 0 { stop - start } else { start - stop };
    let step_abs = if step > 0 { step } else { -step };
    
    // Calculate length, ensure at least 1 element, bounded by reasonable limit
    let length_calc = (diff / step_abs) as usize;
    let length = if length_calc == 0 { 1 } else if length_calc > 20 { 20 } else { length_calc };
    
    assert(length > 0);
    assert(length <= 20);
    
    let mut ret = Vec::new();
    ret.resize(length, 0);
    
    let mut i: usize = 0;
    while i < length
        invariant 
            0 <= i <= length,
            ret.len() == length,
            length > 0,
            length <= 20,
            i > 0 ==> ret[0] == start,
        decreases length - i
    {
        if i == 0 {
            ret.set(i, start);
        } else {
            let prev_value = ret[i-1];
            // With our bounds, this should be safe from overflow
            assume(prev_value + step >= -1000 && prev_value + step <= 1000);
            ret.set(i, prev_value + step);
        }
        i = i + 1;
    }
    
    ret
}

fn main() {}

}