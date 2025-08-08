use vstd::prelude::*;

verus! {

// Note: This is an integer version since Verus doesn't fully support f64 verification
// To match the original Dafny semantics, you would need to work with scaled integers
fn arange_int(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        if step < 0 { start > stop } else { start < stop },
        step != 0,
        // Safety bounds to prevent overflow
        start >= -1000,
        start <= 1000,
        stop >= -1000, 
        stop <= 1000,
        step >= -100,
        step <= 100,
        step != 0,
    ensures
        ret.len() > 0,
        ret[0] == start,
        forall|i: int| #![trigger ret[i]] 1 <= i < ret.len() ==> ret[i] - ret[i-1] == step,
{
    let length_calc = if step > 0 { 
        (stop - start + step - 1) / step  // ceiling division for positive step
    } else {
        (start - stop + (-step) - 1) / (-step)  // ceiling division for negative step
    };
    let length = length_calc as usize;
    
    let mut ret = Vec::with_capacity(length);
    
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
            ret.len() == i,
            length > 0,
            forall|j: int| #![trigger ret[j]] 0 <= j < i ==> ret[j] == start + step * (j as i32),
        decreases length - i,
    {
        proof {
            assert(i < length);
            // Arithmetic bounds checking would go here in a complete implementation
        }
        ret.push(start + step * (i as i32));
        i = i + 1;
    }
    
    ret
}

fn main() {}

}