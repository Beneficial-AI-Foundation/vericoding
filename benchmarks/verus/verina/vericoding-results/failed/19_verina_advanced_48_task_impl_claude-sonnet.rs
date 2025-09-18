// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed indexing to use @ operator for specification contexts */
fn is_sorted(list: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int, j: int| 0 <= i < j < list.len() ==> list@[i] <= list@[j]),
{
    for i in 0..list.len()
        invariant
            forall|k: int, l: int| 0 <= k < l < i ==> list@[k] <= list@[l],
    {
        for j in (i+1)..list.len()
            invariant
                forall|k: int, l: int| 0 <= k < l < i ==> list@[k] <= list@[l],
                forall|l: int| i < l < j ==> list@[i as int] <= list@[l],
        {
            if list[i] > list[j] {
                return false;
            }
        }
    }
    true
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < left.len() ==> left@[i] <= left@[j],
        forall|i: int, j: int| 0 <= i < j < right.len() ==> right@[i] <= right@[j],
    ensures
        result.len() == left.len() + right.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] <= result@[j],
        result@ =~= left@ + right@,
{
    let mut merged: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < left.len() || j < right.len()
        invariant
            i <= left.len(),
            j <= right.len(),
            merged.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < merged.len() ==> merged@[k] <= merged@[l],
            merged@ =~= left@.subrange(0, i as int) + right@.subrange(0, j as int),
        decreases left.len() + right.len() - i - j
    {
        if i == left.len() {
            merged.push(right[j]);
            j += 1;
        } else if j == right.len() {
            merged.push(left[i]);
            i += 1;
        } else if left[i] <= right[j] {
            merged.push(left[i]);
            i += 1;
        } else {
            merged.push(right[j]);
            j += 1;
        }
    }
    
    merged
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
    /* code modified by LLM (iteration 5): Added decreases clause for recursive function */
    if list.len() <= 1 {
        return list;
    }
    
    let mid = list.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    for i in 0..mid {
        left.push(list[i]);
    }
    
    for i in mid..list.len() {
        right.push(list[i]);
    }
    
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    
    merge(sorted_left, sorted_right)
}
// </vc-code>

}
fn main() {}