use vstd::prelude::*;

verus! {

fn main() {}

fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires
        step == 1,
        start < stop,
        0 <= start <= 100,
        0 < stop <= 110,
        stop - start <= 10, // keep length small
    ensures
        ret.len() > 0,
        ret[0] == start,
        ret.len() == (stop - start) as usize,
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == start + i,
        forall|i: int| 1 <= i < ret.len() ==> #[trigger] ret[i] - ret[i-1] == step,
{
    let diff = stop - start;
    let length = diff as usize;
    
    let mut ret: Vec<i32> = Vec::with_capacity(length);
    
    let mut i: usize = 0;
    while i < length
        invariant
            i <= length,
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret[j] == start + j,
            forall|j: int| 1 <= j < i ==> #[trigger] ret[j] - ret[j-1] == 1,
            length <= 10,
            length > 0,
            0 <= start <= 100,
            0 <= start + 10 <= 110, // ensure no overflow in calculations
        decreases length - i,
    {
        let next_val = start + (i as i32);
        ret.push(next_val);
        
        proof {
            // The value we just pushed is at index i
            let old_len = ret.len() - 1;
            assert(old_len == i);
            assert(ret[old_len as int] == next_val);
            assert(ret[i as int] == start + (i as i32));
            
            // Prove the consecutive difference property
            if i > 0 {
                assert(ret[(i-1) as int] == start + ((i-1) as int));
                assert(ret[i as int] - ret[(i-1) as int] 
                    == (start + (i as int)) - (start + ((i-1) as int)));
                assert(ret[i as int] - ret[(i-1) as int] == (i as int) - ((i-1) as int));
                assert(ret[i as int] - ret[(i-1) as int] == 1);
            }
        }
        
        i = i + 1;
    }
    
    ret
}

}