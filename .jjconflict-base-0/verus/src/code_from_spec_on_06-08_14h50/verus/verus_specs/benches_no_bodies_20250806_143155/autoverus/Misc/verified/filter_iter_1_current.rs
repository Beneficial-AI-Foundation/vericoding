use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i += 1;
    }
}
}