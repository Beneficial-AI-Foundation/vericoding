// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < left.len() ==> left[i] <= left[j],
        forall|i: int, j: int| 0 <= i < j < right.len() ==> right[i] <= right[j],
    ensures
        result.len() == left.len() + right.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() == left@.to_multiset() + right@.to_multiset(),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < left.len() && j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            result.len() == i + j,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] <= result[k2],
            left@.to_multiset() + right@.to_multiset() == result@.to_multiset() + left@.subrange(i as int, left.len() as int).to_multiset() + right@.subrange(j as int, right.len() as int).to_multiset(),
            forall|k: int| 0 <= k < result.len() ==> (i < left.len() ==> result[k] <= left[i]),
            forall|k: int| 0 <= k < result.len() ==> (j < right.len() ==> result[k] <= right[j]),
        decreases (left.len() - i) + (right.len() - j)
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i = i + 1;
        } else {
            result.push(right[j]);
            j = j + 1;
        }
    }
    while i < left.len()
        invariant
            j == right.len(),
            0 <= i <= left.len(),
            result.len() == i + j,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] <= result[k2],
            left@.to_multiset() + right@.to_multiset() == result@.to_multiset() + left@.subrange(i as int, left.len() as int).to_multiset(),
            forall|k: int| 0 <= k < result.len() ==> (i < left.len() ==> result[k] <= left[i]),
        decreases left.len() - i
    {
        result.push(left[i]);
        i = i + 1;
    }
    while j < right.len()
        invariant
            i == left.len(),
            0 <= j <= right.len(),
            result.len() == i + j,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] <= result[k2],
            left@.to_multiset() + right@.to_multiset() == result@.to_multiset() + right@.subrange(j as int, right.len() as int).to_multiset(),
            forall|k: int| 0 <= k < result.len() ==> (j < right.len() ==> result[k] <= right[j]),
        decreases right.len() - j
    {
        result.push(right[j]);
        j = j + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected lemma names for seq and multiset */
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mid = n / 2;
    let mut left = Vec::with_capacity(mid);
    let mut i: usize = 0;
    while i < mid
        invariant
            i <= mid,
            left.len() == i,
            left@ == a@.subrange(0, i as int),
        decreases mid - i
    {
        left.push(a[i]);
        i = i + 1;
    }

    let mut right = Vec::with_capacity(n - mid);
    i = mid;
    while i < n
        invariant
            mid <= i <= n,
            right.len() == i - mid,
            right@ == a@.subrange(mid as int, i as int),
        decreases n - i
    {
        right.push(a[i]);
        i = i + 1;
    }

    proof {
        vstd::seq::lemma_subrange_join(a@, 0, mid as int, n as int);
        assert(a@ == left@ + right@);
        vstd::multiset::lemma_to_multiset_distributes_plus(left@, right@);
    }

    let sorted_left = msort(left);
    let sorted_right = msort(right);
    
    let result = merge(sorted_left, sorted_right);
    result
}
// </vc-code>

}
fn main() {}