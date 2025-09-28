// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented lemma proof by case analysis with assertions */
proof fn lemma_filter_preservation(x: Seq<u64>, i: int, elem: u64)
    requires
        0 <= i < x.len(),
        x[i] == elem,
    ensures
        elem % 3 == 0 ==> x.subrange(0, i+1).filter(|k: u64| k % 3 == 0) == x.subrange(0, i).filter(|k: u64| k % 3 == 0).push(elem),
        elem % 3 != 0 ==> x.subrange(0, i+1).filter(|k: u64| k % 3 == 0) == x.subrange(0, i).filter(|k: u64| k % 3 == 0),
{
    proof {
        let prefix = x.subrange(0, i);
        let prefix_plus = x.subrange(0, i+1);
        assert(prefix_plus == prefix.push(elem));
        
        if elem % 3 == 0 {
            assert(prefix_plus.filter(|k: u64| k % 3 == 0) == prefix.filter(|k: u64| k % 3 == 0).push(elem));
        } else {
            assert(prefix_plus.filter(|k: u64| k % 3 == 0) == prefix.filter(|k: u64| k % 3 == 0));
        }
    }
}
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
    /* code modified by LLM (iteration 5): fixed lemma call with correct element parameter */
    for i in 0..x.len()
        invariant
            i <= x.len(),
            y.len() <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
    {
        proof {
            lemma_filter_preservation(x@, i as int, x[i]);
        }
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
}
// </vc-code>

}
fn main() {}