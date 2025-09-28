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
    /* code modified by LLM (iteration 5): fixing type errors in indexing */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.take(i as int).filter(|k: u64| k % 3 == 0),
        decreases x.len() - i,
    {
        let old_y = y@;
        let old_i = i;
        if x[i] % 3 == 0 {
            y.push(x[i]);
            proof {
                assert(y@ == old_y.push(x@[old_i as int]));
                assert(x@.take((old_i + 1) as int) == x@.take(old_i as int).push(x@[old_i as int]));
                assert(x@.take((old_i + 1) as int).filter(|k: u64| k % 3 == 0) == x@.take(old_i as int).filter(|k: u64| k % 3 == 0).push(x@[old_i as int]));
            }
        } else {
            proof {
                assert(y@ == old_y);
                assert(x@.take((old_i + 1) as int).filter(|k: u64| k % 3 == 0) == x@.take(old_i as int).filter(|k: u64| k % 3 == 0));
            }
        }
        i = i + 1;
    }
    proof {
        assert(i == x.len());
        assert(x@.take(x.len() as int) == x@);
    }
}
// </vc-code>

}
fn main() {}