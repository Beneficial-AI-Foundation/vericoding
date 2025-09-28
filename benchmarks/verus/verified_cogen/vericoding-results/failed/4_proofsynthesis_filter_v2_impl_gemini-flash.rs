// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type for Seq::new length. */
spec fn subsequence<T>(s: Seq<T>, start: int, end: int) -> Seq<T>
    recommends 0 <= start <= end <= s.len()
{
    Seq::new((end - start) as nat, |j: int| s.index(start + j))
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
/* code modified by LLM (iteration 5): Fixed dereferencing issue and logic for filter. */
{
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            y@.len() == (x@.subsequence(0, i as int)).filter(|k: u64| k % 3 == 0).len(),
            forall |j: int| 0 <= j < y@.len() ==> y@[j] % 3 == 0,
            forall |j: int| 0 <= j < y@.len() ==> y@[j] == (x@.subsequence(0, i as int)).filter(|k: u64| k % 3 == 0)@[j],
            decreases x.len() - i
    {
        let val = x[i];
        if val % 3 == 0 {
            y.push(val);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}