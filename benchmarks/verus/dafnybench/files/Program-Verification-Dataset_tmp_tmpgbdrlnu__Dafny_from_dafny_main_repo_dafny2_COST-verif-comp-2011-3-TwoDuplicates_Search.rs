// <vc-preamble>
use vstd::prelude::*;

verus! {

uninterp spec fn is_duplicate(a: Seq<int>, p: int) -> bool;

uninterp spec fn is_prefix_duplicate(a: Seq<int>, k: usize, p: int) -> bool;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search(a: &[i32]) -> (ret: (i32, i32))
    requires 
        4 <= a.len(),
        exists|p: int, q: int| #![auto] p != q && is_duplicate(a@.map(|i, x| x as int), p) && is_duplicate(a@.map(|i, x| x as int), q),
        forall|i: usize| #![auto] 0 <= i < a.len() ==> 0 <= a[i as int] < (a.len() - 2) as int,
    ensures ret.0 != ret.1 && is_duplicate(a@.map(|i, x| x as int), ret.0 as int) && is_duplicate(a@.map(|i, x| x as int), ret.1 as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}