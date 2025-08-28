use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for i in 0..x.len()
        invariant
            y.len() == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0).len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
}
// </vc-code>

}

fn main() {}