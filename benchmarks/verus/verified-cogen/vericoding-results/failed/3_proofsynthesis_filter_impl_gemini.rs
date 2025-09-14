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
/* code modified by LLM (iteration 5): Enclosed while loop invariants in curly braces to fix compilation error. */
{
    let mut i: usize = 0;
    while i < x.len()
        decreases x.len() - i
        invariant {
            0 <= i <= x.len() &&
            y@ == old(x)@.subrange(0, i as int).filter(|k: u64| k % 3 == 0)
        }
    {
        let item = x[i];
        if item % 3 == 0 {
            y.push(item);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}