// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &[int], elem: int) -> (p: i32)
    requires sorted(v@)
    ensures 
        -1 <= p < v@.len() &&
        (forall|u: int| 0 <= u <= p ==> v@[u] <= elem) &&
        (forall|w: int| p < w < v@.len() ==> v@[w] > elem)
{
    assume(false);
    -1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search(v: &[int], elem: int) -> (b: bool)
    requires sorted(v@)
    ensures b == v@.contains(elem)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}