// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_permutation(p: Seq<nat>) -> bool {
    p.len() > 0 &&
    (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] >= 1 && #[trigger] p[i] <= p.len()) &&
    (forall|i: int, j: int| 0 <= i < p.len() && 0 <= j < p.len() && i != j ==> #[trigger] p[i] != #[trigger] p[j])
}

spec fn adjacent_sums(p: Seq<nat>) -> Seq<nat> {
    if p.len() < 2 {
        Seq::empty()
    } else {
        Seq::new((p.len() - 1) as nat, |i: int| p[i] + p[i + 1])
    }
}

fn solve_fingerprint(n: usize, p: Vec<nat>) -> (result: Vec<nat>)
    requires 
        n >= 2,
        p.len() == n,
        is_permutation(p@),
    ensures
        result.len() == p.len(),
        is_permutation(result@),
        result@ != p@,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}