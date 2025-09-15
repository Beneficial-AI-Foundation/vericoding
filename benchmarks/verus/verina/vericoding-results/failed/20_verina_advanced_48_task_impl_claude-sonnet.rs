// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to recursive spec function */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn merge_sorted_seqs(left: Seq<i32>, right: Seq<i32>) -> Seq<i32>
    decreases left.len() + right.len()
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if left[0] <= right[0] {
        seq![left[0]] + merge_sorted_seqs(left.subrange(1, left.len() as int), right)
    } else {
        seq![right[0]] + merge_sorted_seqs(left, right.subrange(1, right.len() as int))
    }
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires is_sorted(left@), is_sorted(right@)
    ensures 
        result@ =~= left@ + right@,
        is_sorted(result@)
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            result@ =~= merge_sorted_seqs(left@.subrange(0, i as int), right@.subrange(0, j as int)),
            is_sorted(result@)
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    while i < left.len()
        invariant
            0 <= i <= left.len(),
            j == right.len(),
            result@ =~= merge_sorted_seqs(left@.subrange(0, i as int), right@),
            is_sorted(result@)
    {
        result.push(left[i]);
        i += 1;
    }
    
    while j < right.len()
        invariant
            i == left.len(),
            0 <= j <= right.len(),
            result@ =~= merge_sorted_seqs(left@, right@.subrange(0, j as int)),
            is_sorted(result@)
    {
        result.push(right[j]);
        j += 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implemented merge sort with decreases clause */
    if list.len() <= 1 {
        return list;
    }
    
    let mid = list.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let mut i = 0;
    while i < mid
        invariant
            0 <= i <= mid,
            left.len() == i,
            forall|k: int| 0 <= k < i ==> left[k] == list[k]
    {
        left.push(list[i]);
        i += 1;
    }
    
    while i < list.len()
        invariant
            mid <= i <= list.len(),
            right.len() == i - mid,
            forall|k: int| 0 <= k < i - mid ==> right[k] == list[mid + k]
    {
        right.push(list[i]);
        i += 1;
    }
    
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    
    merge(sorted_left, sorted_right)
}
// </vc-code>

}
fn main() {}