use vstd::prelude::*;

verus! {

fn arange(start: i32, stop: i32, step: i32) -> (ret: Vec<i32>)
    requires 
        step != 0,
        if step > 0 { start < stop } else { start > stop },
        -5 <= start <= 5,
        -5 <= stop <= 5, 
        step == 1 || step == -1,
    ensures
        ret.len() > 0,
        ret[0] == start,
{
    let mut ret: Vec<i32> = Vec::new();
    ret.push(start);
    
    if step > 0 {
        let mut current = start + 1;
        while current < stop && ret.len() < 20
            invariant
                ret.len() > 0,
                ret[0] == start,
                current == start + (ret.len() as i32),
            decreases stop - current,
        {
            ret.push(current);
            current = current + 1;
        }
    } else {
        let mut current = start - 1;
        while current > stop && ret.len() < 20
            invariant
                ret.len() > 0,
                ret[0] == start,
                current == start - (ret.len() as i32),
            decreases current - stop,
        {
            ret.push(current);
            current = current - 1;
        }
    }
    
    ret
}

fn main() {}

}