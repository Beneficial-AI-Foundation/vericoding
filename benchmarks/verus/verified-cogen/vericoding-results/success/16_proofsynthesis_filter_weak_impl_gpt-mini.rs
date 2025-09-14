// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple min function */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate with usize indices and maintain provenance invariant */
    let mut i: usize = 0usize;
    while i < x.len()
        invariant
            i <= x.len(),
            forall |k:int| 0 <= k < y.len() ==> y[k] % 3u64 == 0u64 && exists |j:int| 0 <= j < i as int && x@[j] == y@[k],
        decreases
            x.len() - i
    {
        let v = x[i];
        if v % 3u64 == 0u64 {
            y.push(v);
        }
        i = i + 1;
    }
    proof {
        assert(i == x.len());
        assert(forall |k:int| 0 <= k < y.len() ==> y[k] % 3u64 == 0u64 && x@.contains(y@[k]));
    }
}
// </vc-code>

}
fn main() {}