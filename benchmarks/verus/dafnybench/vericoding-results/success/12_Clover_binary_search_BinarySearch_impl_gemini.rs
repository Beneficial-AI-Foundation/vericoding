// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): re-confirmed correctness of helper lemma */
proof fn lemma_sorted_preserves_order(s: Seq<i32>, i: int, j: int)
    requires
        forall|k: int, l: int| 0 <= k < l < s.len() ==> s[k] <= s[l],
        0 <= i <= j < s.len(),
    ensures
        s[i] <= s[j],
    decreases j - i
{
    if i < j {
        lemma_sorted_preserves_order(s, i, j - 1);
        assert(s[j - 1] <= s[j]);
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], key: i32) -> (n: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] < key,
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
        forall|i: int| n <= i < a.len() ==> a[i] >= key
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added sortedness invariant to fix assertion failures */
    let mut low: usize = 0;
    let mut high: usize = a.len();

    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
            forall|i: int| 0 <= i < low ==> a[i] < key,
            forall|i: int| high <= i < a.len() ==> a[i] >= key,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] < key {
            assert forall|i: int| low <= i <= mid implies a[i] < key by {
                lemma_sorted_preserves_order(a.view(), i, mid as int);
            }
            low = mid + 1;
        } else {
            assert forall|i: int| mid <= i < high implies a[i] >= key by {
                lemma_sorted_preserves_order(a.view(), mid as int, i);
            }
            high = mid;
        }
    }

    low
}
// </vc-code>

}
fn main() {}