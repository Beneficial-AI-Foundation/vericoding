// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_indices(a: &Vec<i32>, indices: &Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
        a[indices[i] as int] <= a[indices[j] as int]
}

spec fn is_stable_sort(a: &Vec<i32>, indices: &Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() && 
        a[indices[i] as int] == a[indices[j] as int] ==> 
        indices[i] < indices[j]
}

spec fn all_indices_valid(a: &Vec<i32>, indices: &Vec<usize>) -> bool {
    forall|i: int| 0 <= i < indices.len() ==> indices[i] < a.len()
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
    /* code modified by LLM (iteration 5): added decreases clause to fix loop verification error */
    let mut indices: Vec<usize> = Vec::new();
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices[j] == j,
            forall|j: int| 0 <= j < i ==> indices[j] < n,
        decreases n - i,
    {
        indices.push(i);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            indices.len() == n,
            forall|k: int| 0 <= k < n ==> indices[k] < n,
            forall|k: int, l: int| 0 <= k < l < i ==> 
                a[indices[k] as int] <= a[indices[l] as int],
            forall|k: int, l: int| 0 <= k < l < i && 
                a[indices[k] as int] == a[indices[l] as int] ==> 
                indices[k] < indices[l],
            forall|k: int, l: int| i <= k < l < n ==> 
                indices[k] < indices[l],
        decreases n - i,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < n,
                i < j <= n,
                indices.len() == n,
                forall|k: int| 0 <= k < n ==> indices[k] < n,
                forall|k: int, l: int| 0 <= k < l < i ==> 
                    a[indices[k] as int] <= a[indices[l] as int],
                forall|k: int, l: int| 0 <= k < l < i && 
                    a[indices[k] as int] == a[indices[l] as int] ==> 
                    indices[k] < indices[l],
                forall|k: int| i <= k < j ==> 
                    a[indices@[i as int] as int] <= a[indices@[k as int] as int],
                forall|k: int| i <= k < j && 
                    a[indices@[i as int] as int] == a[indices@[k as int] as int] ==> 
                    indices@[i as int] < indices@[k as int],
                forall|k: int, l: int| i < k < l < n && (l >= j || k >= j) ==> 
                    indices[k] < indices[l],
            decreases n - j,
        {
            if a[indices[j]] < a[indices[i]] || 
               (a[indices[j]] == a[indices[i]] && indices[j] < indices[i]) {
                let temp = indices[i];
                indices.set(i, indices[j]);
                indices.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    indices
}
// </vc-code>

}
fn main() {}