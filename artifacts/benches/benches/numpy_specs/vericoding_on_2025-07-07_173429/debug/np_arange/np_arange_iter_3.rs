use vstd::prelude::*;

verus! {

fn arange_int(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        ret.len() == ((stop - start) / step) as nat,
        ret.len() > 0,
        ret[0] == start,
        forall|i: int| 1 <= i < ret.len() ==> ret[i] == ret[i-1] + step,
{
    let diff = stop - start;
    let quotient = diff / step;
    let length = quotient as usize;
    
    // Prove length is positive
    if step > 0 {
        assert(start < stop);
        assert(diff > 0);
        assert(quotient > 0);
        assert(length > 0);
    } else {
        assert(start > stop);
        assert(diff < 0);
        assert(quotient > 0);
        assert(length > 0);
    }
    
    let mut ret: Vec<i32> = Vec::new();
    
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= i <= length,
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret[j] == start + step * (j as i32),
            forall|j: int| 1 <= j < i ==> ret[j] == ret[j-1] + step,
        decreases length - i,
    {
        ret.push(start + step * (i as i32));
        i = i + 1;
    }
    
    ret
}

}