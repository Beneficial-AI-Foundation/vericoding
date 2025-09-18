// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): pure element-wise blend without preconditions; guarded indexing to avoid out-of-bounds when lengths differ */
spec fn blend<T>(dst: Seq<T>, src: Seq<T>, mask: Seq<bool>) -> Seq<T> {
    Seq::new(dst.len(), |i: int| if i < src.len() && i < mask.len() && mask[i] { src[i] } else { dst[i] })
}
// </vc-helpers>

// <vc-spec>
fn copyto<T: Copy>(dst: Vec<T>, src: Vec<T>, mask: Vec<bool>) -> (result: Vec<T>)
    requires 
        dst.len() == src.len(),
        dst.len() == mask.len(),
    ensures 
        result.len() == dst.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == if mask[i] { src[i] } else { dst[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement masked copy loop with invariants ensuring element-wise result */
    let n = dst.len();
    let mut out: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            dst.len() == n,
            src.len() == n,
            mask.len() == n,
            out.len() == i,
            0 <= i as int && i as int <= n as int,
            forall|k: int| 0 <= k < i as int ==> out@[k] == (if mask@[k] { src@[k] } else { dst@[k] })
        decreases (n as int) - (i as int)
    {
        assert(i < src.len());
        assert(i < dst.len());
        assert(i < mask.len());
        let val = if mask[i] { src[i] } else { dst[i] };
        out.push(val);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}