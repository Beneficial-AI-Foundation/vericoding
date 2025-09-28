// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant block syntax */
fn partition(arr: &mut Vec<i8>, low: int, high: int) -> (pivot_index: int)
    requires 0 <= low <= high < arr.len(),
    ensures 
        low <= pivot_index <= high,
        forall|i: int| low <= i < pivot_index ==> arr[i] <= arr[pivot_index],
        forall|i: int| pivot_index < i <= high ==> arr[i] >= arr[pivot_index],
{
    let pivot = arr[high as usize];
    let mut i = low - 1;
    
    let mut j = low;
    while j < high
        invariant
            low - 1 <= i < j,
            j <= high,
            forall|k: int| low <= k <= i ==> arr[k] <= pivot,
            forall|k: int| i < k < j ==> arr[k] > pivot,
        decreases high - j
    {
        if arr[j as usize] <= pivot {
            i = i + 1;
            arr.swap(i as usize, j as usize);
        }
        j = j + 1;
    }
    
    arr.swap((i + 1) as usize, high as usize);
    i + 1
}

fn quick_sort_internal(arr: &mut Vec<i8>, low: int, high: int)
    requires 0 <= low <= high < arr.len(),
    ensures forall|i: int, j: int| low <= i <= j <= high ==> arr[i] <= arr[j],
{
    if low < high {
        let pi = partition(arr, low, high);
        if pi > 0 {
            quick_sort_internal(arr, low, pi - 1);
        }
        quick_sort_internal(arr, pi + 1, high);
    }
}

fn sort_vector(arr: &mut Vec<i8>)
    ensures forall|i: int, j: int| 0 <= i <= j < arr.len() ==> arr[i] <= arr[j],
{
    if arr.len() > 0 {
        quick_sort_internal(arr, 0, (arr.len() - 1) as int);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

fn median(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|sorted: Seq<int>| #[trigger] sorted.len() == a@.len() &&
            is_sorted(sorted) &&
            (if a.len() % 2 == 1 {
                result as int == sorted[((a.len() - 1) / 2) as int]
            } else {
                result as int == (sorted[(a.len() / 2 - 1) as int] + sorted[(a.len() / 2) as int]) / 2
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change needed */
    let mut sorted = a.clone();
    sort_vector(&mut sorted);
    
    if sorted.len() % 2 == 1 {
        sorted[((sorted.len() - 1) / 2) as usize]
    } else {
        let mid1 = sorted[(sorted.len() / 2 - 1) as usize] as int;
        let mid2 = sorted[(sorted.len() / 2) as usize] as int;
        ((mid1 + mid2) / 2) as i8
    }
}
// </vc-code>


}
fn main() {}