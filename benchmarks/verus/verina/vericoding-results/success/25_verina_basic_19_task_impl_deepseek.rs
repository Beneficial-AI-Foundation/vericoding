// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma requirements and ordering */
proof fn lemma_sorted_subsequence(a: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| i <= k < j ==> #[trigger] a[k] <= a[k + 1]
    ensures
        a[i] <= a[j]
    decreases j - i
{
    if i < j {
        lemma_sorted_subsequence(a, i + 1, j);
        assert(a[i] <= a[i + 1]);
        assert(a[i + 1] <= a[j]);
    }
}

proof fn lemma_transitive(x: int, y: int, z: int)
    requires x <= y, y <= z
    ensures x <= z
{
}
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant to satisfy initial condition */
    if a.len() <= 1 {
        return true;
    }
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1
            && (i == 0 ==> 0 <= a.len() - 1)
            && forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= a[j + 1]
        decreases (a.len() - 1) - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}