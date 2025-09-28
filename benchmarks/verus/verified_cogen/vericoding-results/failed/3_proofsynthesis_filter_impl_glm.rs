// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added helper function for divisibility by 3 */
spec fn is_divisible_by_3(k: u64) -> bool { k % 3 == 0 }
/* helper modified by LLM (iteration 5): added recursive function to filter sequence */
spec fn filter_divisible_by_3(s: Seq<u64>) -> Seq<u64> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_divisible_by_3(s.drop_last());
        if is_divisible_by_3(s.last()) {
            rest.push(s.last())
        } else {
            rest
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
/* code modified by LLM (iteration 5): replaced filter with custom function in invariant */
{
    let mut i: int = 0;
    while i < x.len() as int
        invariant 0 <= i <= x.len() as int,
        invariant y@ == filter_divisible_by_3(x@.subrange(0, i)),
    {
        let idx: usize = i as usize;
        if x[idx] % 3 == 0 {
            y.push(x[idx]);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}