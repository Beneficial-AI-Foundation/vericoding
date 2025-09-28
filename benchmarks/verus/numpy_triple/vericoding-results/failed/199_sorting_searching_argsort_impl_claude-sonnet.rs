// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
spec fn is_permutation(a: Vec<usize>, n: usize) -> bool {
    a.len() == n &&
    forall|i: int| 0 <= i < n ==> exists|j: int| 0 <= j < n && #[trigger] a[j] == i
}

spec fn is_sorted_by_indices(a: Vec<i8>, indices: Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==>
        a[#[trigger] indices[i] as int] <= a[#[trigger] indices[j] as int]
}

spec fn is_stable_sort(a: Vec<i8>, indices: Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() &&
        a[#[trigger] indices[i] as int] == a[#[trigger] indices[j] as int] ==>
        #[trigger] indices[i] < #[trigger] indices[j]
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
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
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
    let mut result = Vec::new();
    let n = a.len();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k] == k,
        decreases n - i
    {
        result.push(i);
        i += 1;
    }
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] < n,
        decreases n - i
    {
        let mut j = i + 1;
        while j < n
            invariant
                i < n,
                j <= n,
                result.len() == n,
                forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] < n,
            decreases n - j
        {
            if a[result[j]] < a[result[i]] || 
               (a[result[j]] == a[result[i]] && result[j] < result[i]) {
                let temp = result[i];
                result.set(i, result[j]);
                result.set(j, temp);
            }
            j += 1;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}