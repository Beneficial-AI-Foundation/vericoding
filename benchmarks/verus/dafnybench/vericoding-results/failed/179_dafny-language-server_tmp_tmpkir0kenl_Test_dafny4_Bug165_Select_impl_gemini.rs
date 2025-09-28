// <vc-preamble>
use vstd::prelude::*;

verus! {

uninterp spec fn f<T>(a: T) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers are needed */
// </vc-helpers>

// <vc-spec>
fn select<T>(s1: Seq<T>) -> (r: Seq<T>)
    ensures
        forall|e: T| f(e) ==> s1.to_multiset().count(e) == r.to_multiset().count(e),
        forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by changing `ghost let` to `let` */
    let mut r = Seq::<T>::empty();
    let mut i: nat = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|e: T| f(e) ==> s1.subrange(0, i as int).to_multiset().count(e) == r.to_multiset().count(e),
            forall|e: T| !f(e) ==> r.to_multiset().count(e) == 0,
        decreases s1.len() - i
    {
        let e = s1[i as int];
        if f(e) {
            r = r.push(e);
        }
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}