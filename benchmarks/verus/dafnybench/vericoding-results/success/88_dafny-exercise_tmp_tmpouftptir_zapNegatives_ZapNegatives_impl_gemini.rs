// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn zapped_prefix(original: Seq<i32>, current: Seq<i32>, until: int) -> bool {
    forall|i: int| 0 <= i < until ==> 
        if original[i] < 0 { current[i] == 0 } 
        else { current[i] == original[i] }
}

spec fn unchanged_suffix(original: Seq<i32>, current: Seq<i32>, from: int) -> bool {
    forall|i: int| from <= i < original.len() ==> current[i] == original[i]
}
// </vc-helpers>

// <vc-spec>
fn zap_negatives(a: &mut Vec<i32>)
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> 
            if old(a)[i] < 0 { a[i] == 0 } 
            else { a[i] == old(a)[i] }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [Fixed compilation error by using standard indexing `a[i]` instead of `*a.index(i)`.] */
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            zapped_prefix(old(a)@, a@, i as int),
            unchanged_suffix(old(a)@, a@, i as int),
        decreases a.len() - i
    {
        if a[i] < 0 {
            a.set(i, 0);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}