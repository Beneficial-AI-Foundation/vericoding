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
    /* code modified by LLM (iteration 5): corrected standard library lemma calls and proof structure */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
        decreases x.len() - i,
    {
        let element = x[i];
        if element % 3 == 0 {
            y.push(element);
        }

        proof {
            let f = |k: u64| k % 3 == 0;
            vstd::seq_lib::lemma_filter_push_distrib::<u64>(f, x@.subrange(0, i as int), element);
        }

        i = i + 1;
    }
    
    proof {
        vstd::seq_lib::lemma_subrange_total::<u64>(x@);
    }
}
// </vc-code>

}
fn main() {}