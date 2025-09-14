// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_lemma(sorted: Seq<bool>, i: int, j: int)
    requires
        0 <= i < j < sorted.len(),
        forall|k: int| 0 <= k < i ==> !sorted[k],
        forall|k: int| i <= k <= j ==> sorted[k],
        forall|k: int| j < k < sorted.len() ==> sorted[k],
    ensures
        !sorted[i] || sorted[j],
{
}

spec fn is_sorted(arr: Seq<bool>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> !arr[i] || arr[j]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed underflow and multiset invariant */
{
    let n = a.len();
    if n == 0 {
        return;
    }
    let mut left = 0;
    let mut right = n - 1;

    ghost! {
        let initial_multiset = a@.to_multiset();
    }

    while left < right
        invariant
            0 <= left <= right + 1 <= n,
            forall|i: int| 0 <= i < left ==> !a[i],
            forall|i: int| right < i < n ==> a[i],
            a.len() == n,
            a@.to_multiset() == initial_multiset,
        decreases (right - left),
    {
        let left_val = a[left];
        if left_val {
            let right_val = a[right];
            if !right_val {
                a.set(left, right_val);
                a.set(right, left_val);
            }
            right = right - 1;
        } else {
            left = left + 1;
        }
    }
}
// </vc-code>

}
fn main() {}