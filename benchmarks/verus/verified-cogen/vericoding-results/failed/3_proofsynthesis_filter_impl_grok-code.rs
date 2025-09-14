// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unchanged as no issues in helper */
spec fn num_filtered(x: Seq<u64>, i: int) -> int
    requires 0 <= i <= x.len()
    decreases i
{
    if i == 0 { 0int } else { num_filtered(x, i - 1) + if (x@[i - 1] as int) % 3int == 0int { 1int } else { 0int } }
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
    /* code modified by LLM (iteration 5): removed as int from condition to fix compilation error */
    let mut i = 0;
    while i < x.len()
        invariant
            i as int <= x@.len(),
            y@.len() as int == num_filtered(x@, i as int)
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}