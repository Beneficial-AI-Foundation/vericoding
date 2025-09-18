// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified insertion sort with better bounds checking */
spec fn is_sorted_indices(a: Vec<i32>, indices: Vec<usize>) -> bool {
    indices.len() == a.len() &&
    (forall|i: int| 0 <= i < indices.len() ==> indices[i] < a.len()) &&
    (forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
        a[indices[i as int] as int] <= a[indices[j as int] as int]) &&
    (forall|i: int, j: int| 0 <= i < j < indices.len() && 
        a[indices[i as int] as int] == a[indices[j as int] as int] ==> 
        indices[i as int] < indices[j as int])
}

fn insertion_sort_indices(a: Vec<i32>, mut indices: Vec<usize>) -> (result: Vec<usize>)
    requires
        indices.len() == a.len(),
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < a.len(),
        forall|i: int| 0 <= i < indices.len() ==> indices[i] == i
    ensures
        is_sorted_indices(a, result)
{
    if indices.len() <= 1 {
        return indices;
    }
    
    let mut i = 1;
    while i < indices.len()
        invariant
            indices.len() == a.len(),
            1 <= i <= indices.len(),
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> 
                a[indices[j as int] as int] <= a[indices[k as int] as int],
            forall|j: int, k: int| 0 <= j < k < i && 
                a[indices[j as int] as int] == a[indices[k as int] as int] ==> 
                indices[j as int] < indices[k as int]
        decreases indices.len() - i
    {
        let key = indices[i];
        let mut j = i;
        while j > 0
            invariant
                0 <= j <= i < indices.len(),
                indices.len() == a.len(),
                key < a.len(),
                forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len()
            decreases j
        {
            if j > 0 && (a[indices[j - 1]] > a[key] || 
                        (a[indices[j - 1]] == a[key] && 
                         indices[j - 1] > key)) {
                indices.set(j, indices[j - 1]);
                j = j - 1;
            } else {
                break;
            }
        }
        indices.set(j, key);
        i = i + 1;
    }
    indices
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed initial invariant for i=0 case */
    let mut indices = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices[j] == j
        decreases a.len() - i
    {
        indices.push(i);
        i = i + 1;
    }
    
    proof {
        assert(indices.len() == a.len());
        assert(forall|j: int| 0 <= j < indices.len() ==> indices[j] == j);
        assert(forall|j: int| 0 <= j < indices.len() ==> indices[j] < a.len());
    }
    
    insertion_sort_indices(a, indices)
}
// </vc-code>

}
fn main() {}