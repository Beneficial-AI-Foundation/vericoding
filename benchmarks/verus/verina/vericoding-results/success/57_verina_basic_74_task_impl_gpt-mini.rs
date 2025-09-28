// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): convert usize to int for specs */
spec fn usize_to_int(x: usize) -> int { x as int }
// </vc-helpers>

// <vc-spec>
fn max_array(a: &Vec<i32>) -> (result: i32)
    requires max_array_precond(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        exists|k: int| 0 <= k < a.len() && result == a[k],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): fixed index types and loop invariants */
    let mut i: usize = 1;
    let mut max: i32 = a[0];
    let mut idx: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            forall|k: int| 0 <= k < i as int ==> max >= a[k],
            exists|k: int| 0 <= k < i as int && max == a[k],
        decreases (a.len() as int) - (i as int)
    {
        if a[i] > max {
            max = a[i];
            idx = i;
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|k: int| 0 <= k < a.len() as int ==> max >= a[k]);
        assert(exists|k: int| 0 <= k < a.len() as int && max == a[k]);
    }
    max
}
// </vc-code>

}
fn main() {}