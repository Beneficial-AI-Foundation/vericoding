// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch in ghost_i increment by specifying 1 as usize */
    let mut i = 0usize;
    let ghost mut ghost_i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            ghost_i == i,
            y@ == x@.subrange(0, ghost_i as int).filter(|k: u64| k % 3 == 0),
        decreases (x.len() - i)
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
            proof {
                ghost_i = ghost_i + (1usize);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}