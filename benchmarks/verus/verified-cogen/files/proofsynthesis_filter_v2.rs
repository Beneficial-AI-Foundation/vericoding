use vstd::prelude::*;

verus!{

fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
{
    assume(false);
    unreached()
}

}
fn main() {}