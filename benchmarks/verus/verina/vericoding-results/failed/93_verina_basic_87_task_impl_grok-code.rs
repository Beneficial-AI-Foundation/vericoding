// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min_index(start: usize, end: usize, a: &[i32]) -> usize
    requires
        start < end <= a.len(),
    ensures
        start <= result < end,
        forall|k: int| start <= k < end ==> a[k] >= a[result],
{
    let mut min_idx = start;
    let mut j = start + 1;
    while j < end {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    let mut result = a.clone();
    let len = result.len();
    let mut i = 0;
    while i < len - 1 {
        let min_idx = find_min_index(i, len, &result);
        result.swap(i, min_idx);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}