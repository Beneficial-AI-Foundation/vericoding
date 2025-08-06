use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    for i in 0..x.len()
        invariant
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
}
}