// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn partition_point(s: Seq<i32>, pivot: i32) -> int {
    if s.len() == 0 {
        0
    } else {
        choose|k: int| 0 <= k <= s.len() && forall|i: int| 0 <= i < k ==> s[i] <= pivot && forall|i: int| k <= i < s.len() ==> s[i] > pivot
    }
}

/* helper modified by LLM (iteration 5): Fixed decreases clause in all loops */
fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted(left@),
        sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        sorted(result@),
        result@.to_multiset() =~= left@.to_multiset().add(right@.to_multiset()),
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < left.len() && j < right.len()
        invariant
            i <= left.len(),
            j <= right.len(),
            result@.len() == i + j,
            sorted(result@),
            forall|k: int| 0 <= k < i ==> left[k] <= result[result.len() - 1] || result.len() == 0,
            forall|k: int| 0 <= k < j ==> right[k] <= result[result.len() - 1] || result.len() == 0,
            result@.to_multiset() =~= left@.subrange(0, i as int).to_multiset().add(right@.subrange(0, j as int).to_multiset()),
        decreases left.len() + right.len() - i - j,
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
            i <= left.len(),
            j == right.len(),
            result@.len() == i + j,
            sorted(result@),
            result@.to_multiset() =~= left@.subrange(0, i as int).to_multiset().add(right@.to_multiset()),
        decreases left.len() - i,
    {
        result.push(left[i]);
        i = i + 1;
    }
    
    while j < right.len()
        invariant
            i == left.len(),
            j <= right.len(),
            result@.len() == i + j,
            sorted(result@),
            result@.to_multiset() =~= left@.to_multiset().add(right@.subrange(0, j as int).to_multiset()),
        decreases right.len() - j,
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
decreases a.len(),
{
    /* code modified by LLM (iteration 5): Fixed decreases clause placement */
    
    if a.len() <= 1 {
        return a;
    }
    
    let mid = a.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    for i in 0..mid
        invariant
            left@.len() == i,
            left@.to_multiset() =~= a@.subrange(0, i as int).to_multiset(),
    {
        left.push(a[i]);
    }
    
    for i in mid..a.len()
        invariant
            right@.len() == i - mid,
            right@.to_multiset() =~= a@.subrange(mid as int, i as int).to_multiset(),
    {
        right.push(a[i]);
    }
    
    let sorted_left = msort(left);
    let sorted_right = msort(right);
    merge(sorted_left, sorted_right)
}
// </vc-code>

}
fn main() {}