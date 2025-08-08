use vstd::prelude::*;

verus! {

fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        if step < 0 { start > stop } else { start < stop },
        step != 0,
    ensures
        ret.len() == ((stop as int - start as int) / step as int) as nat,
        ret.len() > 0,
        ret[0] == start,
        forall|i: int| 1 <= i < ret.len() ==> #[trigger] ret[i] == ret[i-1] + step,
{
    let length = ((stop - start) / step) as usize;
    let mut ret = Vec::with_capacity(length);
    
    let mut i = 0;
    while i < length
        invariant
            0 <= i <= length,
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] ret[j] == start + step * j,
        decreases length - i,
    {
        ret.push(start + step * (i as i32));
        i = i + 1;
    }
    
    ret
}

}