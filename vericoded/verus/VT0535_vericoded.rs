// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate to state a <= x <= b */
pub open spec fn between(a: int, x: int, b: int) -> bool {
    a <= x && x <= b
}
// </vc-helpers>

// <vc-spec>
fn getdomain(x: Vec<i8>) -> (result: Vec<i8>)
    requires x@.len() > 0,
    ensures
        result@.len() == 2,
        result@[0] as int <= result@[1] as int,
        forall|i: int| 0 <= i < x@.len() ==> result@[0] as int <= x@[i] as int && x@[i] as int <= result@[1] as int,
        exists|i: int| 0 <= i < x@.len() && x@[i] as int == result@[0] as int,
        exists|j: int| 0 <= j < x@.len() && x@[j] as int == result@[1] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): single-pass min/max using values with inductive invariants over the processed prefix */
    let mut minv: i8 = x[0];
    let mut maxv: i8 = x[0];
    let mut i: usize = 1;
    while i < x.len()
        invariant
            1 <= i as int && i as int <= x@.len(),
            minv as int <= maxv as int,
            forall|j: int| 0 <= j && j < i as int ==> between(minv as int, x@[j] as int, maxv as int),
            exists|j: int| 0 <= j && j < i as int && x@[j] as int == minv as int,
            exists|j: int| 0 <= j && j < i as int && x@[j] as int == maxv as int,
        decreases x@.len() - i as int
    {
        let xi = x[i];
        if xi < minv {
            proof {
                assert(minv as int <= maxv as int);
                assert((xi as int) < (minv as int));
                assert((xi as int) <= (maxv as int));
            }
            minv = xi;
        } else if xi > maxv {
            maxv = xi;
        }
        i = i + 1;
    }

    let mut r: Vec<i8> = Vec::new();
    r.push(minv);
    r.push(maxv);
    r
}
// </vc-code>


}
fn main() {}