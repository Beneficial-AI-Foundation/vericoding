// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to check if a vector is sorted
spec fn is_sorted(v: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] as int <= v[j] as int
}

// Helper function to merge two sorted vectors
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn merge(left: Vec<i8>, right: Vec<i8>) -> (result: Vec<i8>)
    requires
        is_sorted(left@),
        is_sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        is_sorted(result@),
        result@.to_multiset() =~= left@.to_multiset().add(right@.to_multiset()),
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < left.len() || j < right.len()
        invariant
            i <= left.len(),
            j <= right.len(),
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() =~= left@.subrange(0, i as int).to_multiset().add(right@.subrange(0, j as int).to_multiset()),
        decreases (left.len() - i) + (right.len() - j)
    {
        if i >= left.len() {
            result.push(right[j]);
            j += 1;
        } else if j >= right.len() {
            result.push(left[i]);
            i += 1;
        } else if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    result
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
{
    /* code modified by LLM (iteration 5): added decreases clause to recursive function */
    if a.len() <= 1 {
        return a;
    }
    
    let mid = a.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let mut i = 0;
    while i < mid
        invariant
            i <= mid,
            left.len() == i,
            forall|k: int| 0 <= k < i ==> left[k] == a[k],
        decreases mid - i
    {
        left.push(a[i]);
        i += 1;
    }
    
    while i < a.len()
        invariant
            mid <= i <= a.len(),
            right.len() == i - mid,
            forall|k: int| 0 <= k < i - mid ==> right[k] == a[mid + k],
        decreases a.len() - i
    {
        right.push(a[i]);
        i += 1;
    }
    
    let sorted_left = msort(left);
    let sorted_right = msort(right);
    
    merge(sorted_left, sorted_right)
}
// </vc-code>

}
fn main() {}