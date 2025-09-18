// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed vector slicing to use proper usize indexing */
spec fn is_sorted(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(left),
        is_sorted(right),
    ensures
        is_sorted(result),
        result@ =~= left@ + right@,
    decreases left.len() + right.len(),
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else {
        if left[0] <= right[0] {
            let mut left_slice = Vec::new();
            for i in 1..left.len() {
                left_slice.push(left[i]);
            }
            let mut merged = merge(left_slice, right);
            merged.insert(0, left[0]);
            merged
        } else {
            let mut right_slice = Vec::new();
            for i in 1..right.len() {
                right_slice.push(right[i]);
            }
            let mut merged = merge(left, right_slice);
            merged.insert(0, right[0]);
            merged
        }
    }
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
/* code modified by LLM (iteration 2): fixed vector slicing to use proper usize indexing */
{
    if list.len() <= 1 {
        list
    } else {
        let mid = list.len() / 2;
        let mut left_slice = Vec::new();
        for i in 0..mid {
            left_slice.push(list[i]);
        }
        let mut right_slice = Vec::new();
        for i in mid..list.len() {
            right_slice.push(list[i]);
        }
        let left = merge_sort(left_slice);
        let right = merge_sort(right_slice);
        merge(left, right)
    }
}
// </vc-code>

}
fn main() {}