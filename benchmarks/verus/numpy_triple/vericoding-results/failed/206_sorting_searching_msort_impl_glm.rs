// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed multiset union using + operator */
fn merge(left: Vec<i8>, right: Vec<i8>) -> (result: Vec<i8>)
    requires
        left.len() >= 0,
        right.len() >= 0,
        forall|i: int, j: int| 0 <= i < j < left.len() ==> left[i] as int <= left[j] as int,
        forall|i: int, j: int| 0 <= i < j < right.len() ==> right[i] as int <= right[j] as int,
    ensures
        result.len() == left.len() + right.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= left@.to_multiset() + right@.to_multiset(),
{
    let mut merged = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() || j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            merged.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < merged.len() ==> merged[k] as int <= merged[l] as int,
            merged@.to_multiset() =~= left@.subrange(0, i as int).to_multiset() + right@.subrange(0, j as int).to_multiset(),
        decreases (left.len() - i) + (right.len() - j),
    {
        if i < left.len() && (j >= right.len() || left[i] <= right[j]) {
            merged.push(left[i]);
            i += 1;
        } else {
            merged.push(right[j]);
            j += 1;
        }
    }
    
    merged
}

/* helper modified by LLM (iteration 4): changed indices from int to usize for merge_sort_helper */
fn merge_sort_helper(a: Vec<i8>, start: usize, end: usize) -> (result: Vec<i8>)
    requires
        0 <= start <= end <= a.len(),
    ensures
        result.len() == end - start,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.subrange(start as int, end as int).to_multiset(),
{
    if end - start <= 1 {
        let mut slice = Vec::new();
        if start < end {
            slice.push(a[start]);
        }
        slice
    } else {
        let mid = start + (end - start) / 2;
        let left_sorted = merge_sort_helper(a, start, mid);
        let right_sorted = merge_sort_helper(a, mid, end);
        merge(left_sorted, right_sorted)
    }
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): removed int conversion for len parameter */
{
    let len = a.len();
    merge_sort_helper(a, 0, len)
}
// </vc-code>

}
fn main() {}