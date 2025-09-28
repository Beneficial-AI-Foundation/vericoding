// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed loop invariant and filter logic */
fn build_filtered_vec(x: &Vec<u64>) -> (v: Vec<u64>)
    ensures v@ == x@.filter(|k:u64| k%3 == 0)
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant 
            i <= x.len(),
            v@ == x@.subrange(0, i as int).filter(|k: u64| k%3 == 0)
        decreases x.len() - i
    {
        if x[i] % 3 == 0 {
            v.push(x[i]);
            assert(x@.subrange(0, (i + 1) as int).filter(|k: u64| k%3 == 0) == v@);
        } else {
            assert(x@.subrange(0, (i + 1) as int).filter(|k: u64| k%3 == 0) == v@);
        }
        i = i + 1;
    }
    assert(v@ == x@.filter(|k: u64| k%3 == 0));
    v
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
/* code modified by LLM (iteration 5): unchanged as helper fix resolves verification issues */
{
    *y = build_filtered_vec(x);
}
// </vc-code>

}
fn main() {}