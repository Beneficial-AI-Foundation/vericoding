use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn filter_spec(s: Seq<u64>, pred: spec_fn(u64) -> bool) -> Seq<u64> {
    s.filter(pred)
}

spec fn divisible_by_3(k: u64) -> bool {
    k % 3 == 0
}
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
            y@.len() <= i,
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
            proof {
                assert(x@.subrange(0, (i + 1) as int) == x@.subrange(0, i as int).push(x@[i as int]));
                assert(x@[i as int] % 3 == 0);
                assert(y@ == x@.subrange(0, (i + 1) as int).filter(|k:u64| k%3 == 0));
            }
        } else {
            proof {
                assert(x@.subrange(0, (i + 1) as int) == x@.subrange(0, i as int).push(x@[i as int]));
                assert(x@[i as int] % 3 != 0);
                assert(y@ == x@.subrange(0, (i + 1) as int).filter(|k:u64| k%3 == 0));
            }
        }
    }
    proof {
        assert(x@.subrange(0, x@.len() as int) == x@);
    }
}
// </vc-code>

}

fn main() {}