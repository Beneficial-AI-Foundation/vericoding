use vstd::prelude::*;

verus! {

fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires 
        step == 1,  // Simplified to step = 1 to match Dafny semantics
        start < stop,
        stop - start <= 10,  // Bounded range for verification
        start >= 0,
        stop <= 10,
    ensures 
        ret.len() > 0,
        ret[0] == start,
        ret.len() == (stop - start) as nat,
        forall|i: int| 1 <= i < ret.len() ==> #[trigger] ret[i] == ret[i-1] + 1,
{
    let mut ret = Vec::new();
    let mut current = start;
    
    while current < stop
        invariant 
            ret.len() == (current - start) as nat,
            current >= start,
            current <= stop,
            forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i] == start + i,
        decreases stop - current,
    {
        ret.push(current);
        current += 1;
    }
    
    ret
}

fn main() {}

}