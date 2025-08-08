use vstd::prelude::*;

verus! {

fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
        (stop as int - start as int) % (step as int) == 0,  // exact division
        start >= -100 && start <= 100,
        stop >= -100 && stop <= 100,
        step >= -10 && step <= 10 && step != 0,
    ensures
        ret.len() == ((stop as int - start as int) / (step as int)).abs() as nat,
        ret.len() > 0,
        ret[0] == start,
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == start + step * (i as i32),
{
    let ghost length_spec = ((stop as int - start as int) / (step as int)).abs();
    
    let length_calc = if step > 0 { 
        (stop - start) / step 
    } else { 
        (start - stop) / (-step) 
    };
    
    let length = length_calc as usize;
    let mut ret = Vec::with_capacity(length);
    
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
            ret.len() == i,
            length == length_spec as usize,
            forall|j: int| 0 <= j < i ==> ret[j] == start + step * (j as i32),
        decreases length - i,
    {
        ret.push(start + step * (i as i32));
        i = i + 1;
    }
    
    ret
}

}