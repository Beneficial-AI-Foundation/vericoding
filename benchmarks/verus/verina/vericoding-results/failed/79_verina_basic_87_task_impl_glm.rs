// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed loop variable to int to avoid casting in invariant */
fn find_min_index(arr: &Vec<i32>, start: usize, end: usize) -> (result: usize)
    requires
        start <= end,
        end < arr.len(),
    ensures
        start as int <= result as int <= end as int,
        forall|i: int| start as int <= i <= end as int ==> arr[result as int] <= arr[i]
{
    let mut min_idx = start;
    let mut i: int = (start + 1) as int;
    while i <= end as int
        invariant
            start as int <= min_idx as int,
            min_idx as int < i,
            forall|j: int| start as int <= j < i ==> arr[min_idx as int] <= arr[j]
        decreases (end as int - i)
    {
        if arr[i as usize] < arr[min_idx] {
            min_idx = i as usize;
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): fixed invariant condition for cross-array comparison */
    let mut arr = a.clone();
    let mut result = Vec::new();
    while !arr.is_empty()
        invariant
            result@ + arr@ =~= a@,
            forall|i: int, j: int| 0 <= i <= j < result.len() as int ==> result[i] <= result[j],
            forall|i: int, j: int| 
                0 <= i < result.len() as int && 
                0 <= j < arr.len() as int 
                ==> result[i] <= arr[j]
        decreases arr.len() as int
    {
        let min_idx = find_min_index(&arr, 0, arr.len()-1);
        let min_val = arr.remove(min_idx);
        result.push(min_val);
    }
    result
}
// </vc-code>

}
fn main() {}