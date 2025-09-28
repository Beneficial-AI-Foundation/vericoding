// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn selection_sort_indices(a: Vec<i8>) -> Vec<usize>
    ensures
        result.len() == a.len(),
        forall|k: int| 0 <= k && k < a.len() as int ==> (exists|i: int| 0 <= i && i < result.len() && result@[i] as int == k),
        forall|i: int| 0 <= i && i < result.len() ==> forall|j: int| 0 <= j && j < result.len() && i != j ==> result@[i] != result@[j],
        forall|i: int| 0 <= i && i+1 < result.len() ==> a@[result@[i] as int] <= a@[result@[i+1] as int],
{
    let n = a.len();

    let mut rem = Vec::<usize>::new();
    let mut i = 0usize;
    while i < n
        invariant
            rem.len() == i,
            forall|t: int| 0 <= t && t < i as int ==> rem@[t] as int == t,
        decreases n - i
    {
        rem.push(i);
        i += 1;
    }

    let mut result = Vec::<usize>::new();
    while rem.len() > 0
        invariant
            result.len() + rem.len() == n,
            forall|x:int| 0 <= x && x < result.len() ==> 0 <= result@[x] && result@[x] as int < n as int,
            forall|x:int| 0 <= x && x < rem.len() ==> 0 <= rem@[x] && rem@[x] as int < n as int,
            forall|u:int, v:int| 0 <= u && u < result.len() && 0 <= v && v < rem.len() ==> result@[u] != rem@[v],
            forall|i:int, j:int| 0 <= i && i < result.len() && 0 <= j && j < rem.len() ==> a@[result@[i] as int] <= a@[rem@[j] as int],
        decreases rem.len()
    {
        let mut pos = 0usize;
        let mut j = 1usize;
        while j < rem.len()
            invariant
                j <= rem.len(),
                pos < rem.len(),
                forall|t:int| 0 <= t && t < j as int ==> a@[rem@[pos] as int] <= a@[rem@[t] as int],
            decreases rem.len() - j
        {
            if a@[rem@[j] as int] < a@[rem@[pos] as int] {
                pos = j;
            }
            j += 1;
        }
        let idx = rem.remove(pos);
        result.push(idx);
    }

    result
}

// </vc-helpers>

// <vc-spec>
fn argpartition(a: Vec<i8>, kth: usize) -> (indices: Vec<usize>)
    requires 
        a.len() > 0,
        kth < a.len(),
    ensures
        /* The indices form a valid permutation of 0..n-1 */
        indices.len() == a.len(),
        /* Partition property: all elements before kth position are ≤ kth element */
        forall|i: int| 0 <= i < kth ==> a@[#[trigger] indices@[i] as int] <= a@[#[trigger] indices@[kth as int] as int],
        /* Partition property: all elements after kth position are ≥ kth element */
        forall|i: int| kth < i && i < indices.len() ==> a@[#[trigger] indices@[kth as int] as int] <= a@[#[trigger] indices@[i] as int],
// </vc-spec>
// <vc-code>
{
    let indices = selection_sort_indices(a);
    indices
}

// </vc-code>


}
fn main() {}