// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for equality of first k elements */
spec fn prefix_equal(a1: Vec<f32>, a2: Vec<f32>, k: int) -> bool { 0 <= k && k <= a1.len() && (forall|i: int| 0 <= i && i < k ==> a1[i] == a2[i]) }
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and compare elements with inline prefix invariant */
    let mut i: int = 0;
    let n: int = a1.len();
    while i < n
        invariant 0 <= i && i <= n
        invariant forall|j: int| 0 <= j && j < i ==> a1[j] == a2[j]
        decreases n - i
    {
        if a1[i] != a2[i] {
            return false;
        } else {
            proof {
                assert(0 <= i && i < n);
                assert(a1[i] == a2[i]);
                assert(forall|j: int| 0 <= j && j < i ==> a1[j] == a2[j]);
                assert(forall|j: int| 0 <= j && j < i + 1 ==> a1[j] == a2[j]);
            }
        }
        i = i + 1;
    }
    proof {
        assert(!(i < n));
        assert(i >= n);
        assert(i == n);
        assert(forall|j: int| 0 <= j && j < i ==> a1[j] == a2[j]);
        assert(forall|j: int| 0 <= j && j < n ==> a1[j] == a2[j]);
    }
    true
}
// </vc-code>

}
fn main() {}