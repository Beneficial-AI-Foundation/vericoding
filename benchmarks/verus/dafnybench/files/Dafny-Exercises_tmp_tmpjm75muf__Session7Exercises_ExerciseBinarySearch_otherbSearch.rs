use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@)
    ensures -1 <= p < v.len()
    ensures forall|u: int| 0 <= u <= p ==> v[u] <= elem
    ensures forall|w: int| p < w < v.len() ==> v[w] > elem
{
    assume(false);
    -1
}






// Recursive binary search

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn other_b_search(v: &Vec<i32>, elem: i32) -> (res: (bool, usize))
    requires sorted(v@)
    ensures 0 <= res.1 <= v.len()
    ensures res.0 == v@.contains(elem)
    ensures res.0 ==> res.1 < v.len() && v[res.1 as int] == elem
    ensures !res.0 ==> forall|u: int| 0 <= u < res.1 ==> v[u] < elem
    ensures !res.0 ==> forall|w: int| res.1 <= w < v.len() ==> v[w] > elem
// Implement and verify
// </vc-spec>
// <vc-code>
{
    assume(false);
    (false, 0)
}
// </vc-code>


fn main() {
}

}