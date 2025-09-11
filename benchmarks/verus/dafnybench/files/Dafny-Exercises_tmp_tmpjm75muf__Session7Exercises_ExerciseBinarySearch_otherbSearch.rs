// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@),
    ensures -1 <= p < v.len(),
            (forall|u: int| 0 <= u <= p ==> v[u] <= elem),
            (forall|w: int| p < w < v.len() ==> v[w] > elem),
{
    assume(false);
    -1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn other_b_search(v: &Vec<i32>, elem: i32) -> (res: (bool, usize))
    requires sorted(v@)
    ensures 
        0 <= res.1 <= v.len(),
        res.0 == v@.contains(elem),
        res.0 ==> res.1 < v.len() && v[res.1 as int] == elem,
        !res.0 ==> forall|u: int| 0 <= u < res.1 ==> v[u] < elem,
        !res.0 ==> forall|w: int| res.1 <= w < v.len() ==> v[w] > elem
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}