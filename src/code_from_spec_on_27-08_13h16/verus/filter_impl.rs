use vstd::prelude::*;

verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@.len() <= i,
            forall |j: usize| j < y@.len() ==> (y@[j] % 3) == 0,
            y@ == x@.subrange(0, i as int).filter(|k: u64| (k % 3) == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}