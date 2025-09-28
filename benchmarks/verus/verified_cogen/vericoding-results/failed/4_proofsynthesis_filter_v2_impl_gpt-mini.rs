// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified recursive prefix_filter returning prefix ignoring divisibility */ spec fn prefix_filter(s: Seq<u64>, i: nat) -> Seq<u64> decreases i { if i == 0 { Seq::empty() } else { prefix_filter(s, i - 1) } }
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
    /* code modified by LLM (iteration 5): iterate with usize index and maintain prefix_filter invariant (simplified helper) */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            y@ == prefix_filter(x@, i as nat),
            (i as nat) <= x@.len(),
        decreases x@.len() - (i as nat)
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