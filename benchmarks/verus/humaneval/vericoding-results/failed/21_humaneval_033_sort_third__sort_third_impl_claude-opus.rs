// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clauses to all while loops */
spec fn is_sorted_thirds(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() && i % 3 == 0 && j % 3 == 0 ==> s[i] <= s[j]
}

spec fn preserves_non_thirds(original: Seq<i8>, result: Seq<i8>) -> bool {
    forall|i: int| 0 <= i < original.len() && i % 3 != 0 ==> result[i] == original[i]
}

fn extract_thirds(a: &Vec<i8>) -> (result: (Vec<i8>, Vec<usize>))
    requires a@.len() > 0
    ensures
        result.0@.len() == result.1@.len(),
        forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] < a@.len(),
        forall|i: int| 0 <= i < result.1@.len() ==> result.1@[i] % 3 == 0,
        forall|i: int| 0 <= i < result.1@.len() ==> result.0@[i] == a@[result.1@[i] as int],
        forall|i: int, j: int| 0 <= i < j < result.1@.len() ==> result.1@[i] < result.1@[j],
        forall|k: int| 0 <= k < a@.len() && k % 3 == 0 ==> exists|i: int| 0 <= i < result.1@.len() && result.1@[i] == k
{
    let mut thirds = Vec::new();
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a@.len(),
            thirds@.len() == indices@.len(),
            forall|j: int| 0 <= j < indices@.len() ==> indices@[j] < i,
            forall|j: int| 0 <= j < indices@.len() ==> indices@[j] % 3 == 0,
            forall|j: int| 0 <= j < indices@.len() ==> thirds@[j] == a@[indices@[j] as int],
            forall|j1: int, j2: int| 0 <= j1 < j2 < indices@.len() ==> indices@[j1] < indices@[j2],
            forall|k: int| 0 <= k < i && k % 3 == 0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] == k,
        decreases a.len() - i
    {
        if i % 3 == 0 {
            thirds.push(a[i]);
            indices.push(i);
        }
        i = i + 1;
    }
    
    (thirds, indices)
}

fn sort_i8_vec(v: &Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == v@.len(),
        result@.to_multiset() == v@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j]
{
    let mut sorted = v.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n - 1
        invariant
            sorted@.len() == v@.len(),
            sorted@.to_multiset() == v@.to_multiset(),
            forall|j: int, k: int| 0 <= j < i && i <= k < sorted@.len() ==> sorted@[j] <= sorted@[k],
            forall|j: int, k: int| 0 <= j < k <= i ==> sorted@[j] <= sorted@[k],
        decreases n - 1 - i
    {
        let mut j: usize = i + 1;
        let mut min_idx = i;
        let mut min_val = sorted[i];
        
        while j < n
            invariant
                i < j <= n,
                i <= min_idx < j,
                min_idx < sorted@.len(),
                min_val == sorted@[min_idx as int],
                forall|k: int| i <= k < j ==> sorted@[min_idx as int] <= sorted@[k],
                sorted@.len() == v@.len(),
                sorted@.to_multiset() == v@.to_multiset(),
            decreases n - j
        {
            if sorted[j] < min_val {
                min_idx = j;
                min_val = sorted[j];
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let (thirds, indices) = extract_thirds(a);
    let sorted_thirds = sort_i8_vec(&thirds);
    
    let mut result = a.clone();
    let mut i: usize = 0;
    
    while i < indices.len()
        invariant
            i <= indices@.len(),
            indices@.len() == sorted_thirds@.len(),
            result@.len() == a@.len(),
            forall|j: int| 0 <= j < indices@.len() ==> indices@[j] < result@.len(),
            forall|j: int| 0 <= j < i ==> result@[indices@[j] as int] == sorted_thirds@[j],
            forall|j: int| i <= j < indices@.len() ==> result@[indices@[j] as int] == a@[indices@[j] as int],
            forall|k: int| 0 <= k < result@.len() && k % 3 != 0 ==> result@[k] == a@[k],
            forall|k: int| 0 <= k < result@.len() && k % 3 == 0 && !exists|j: int| 0 <= j < i && indices@[j] == k ==> result@[k] == a@[k],
            result@.to_multiset() == a@.to_multiset(),
        decreases indices.len() - i
    {
        result.set(indices[i], sorted_thirds[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}