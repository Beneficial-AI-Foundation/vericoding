// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed indexing by using proper int types and sequence operations */
fn sorted(v: Vec<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] <= v@[j]
}

fn no_duplicates(v: Vec<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> v@[i] != v@[j]
}

fn merge_sorted(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    requires
        sorted(ar1),
        sorted(ar2),
        no_duplicates(ar1),
        no_duplicates(ar2),
    ensures
        sorted(result),
        no_duplicates(result),
        forall|i: int| 0 <= i < ar1.len() ==> result@.contains(ar1@[i]),
        forall|i: int| 0 <= i < ar2.len() ==> result@.contains(ar2@[i]),
        forall|j: int| 0 <= j < result.len() ==> ar1@.contains(result@[j]) || ar2@.contains(result@[j])
{
    let mut i: int = 0;
    let mut j: int = 0;
    let mut result = Vec::new();
    
    while i < ar1.len() && j < ar2.len()
        invariant
            0 <= i <= ar1.len(),
            0 <= j <= ar2.len(),
            sorted(result),
            no_duplicates(result),
            forall|k: int| 0 <= k < ar1.len() && k < i ==> result@.contains(ar1@[k]),
            forall|k: int| 0 <= k < ar2.len() && k < j ==> result@.contains(ar2@[k]),
            forall|k: int| 0 <= k < result.len() ==> ar1@.contains(result@[k]) || ar2@.contains(result@[k])
        decreases ar1.len() - i + ar2.len() - j
    {
        if ar1@[i] < ar2@[j] {
            result.push(ar1@[i]);
            i += 1;
        } else if ar1@[i] > ar2@[j] {
            result.push(ar2@[j]);
            j += 1;
        } else {
            result.push(ar1@[i]);
            i += 1;
            j += 1;
        }
    }
    
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            j == ar2.len(),
            sorted(result),
            no_duplicates(result),
            forall|k: int| 0 <= k < ar1.len() && k < i ==> result@.contains(ar1@[k]),
            forall|k: int| 0 <= k < ar2.len() ==> result@.contains(ar2@[k]),
            forall|k: int| 0 <= k < result.len() ==> ar1@.contains(result@[k]) || ar2@.contains(result@[k])
        decreases ar1.len() - i
    {
        result.push(ar1@[i]);
        i += 1;
    }
    
    while j < ar2.len()
        invariant
            i == ar1.len(),
            0 <= j <= ar2.len(),
            sorted(result),
            no_duplicates(result),
            forall|k: int| 0 <= k < ar1.len() ==> result@.contains(ar1@[k]),
            forall|k: int| 0 <= k < ar2.len() && k < j ==> result@.contains(ar2@[k]),
            forall|k: int| 0 <= k < result.len() ==> ar1@.contains(result@[k]) || ar2@.contains(result@[k])
        decreases ar2.len() - j
    {
        result.push(ar2@[j]);
        j += 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn union1d(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        /* Union property: every element from either input array is in result */
        forall|i: int| 0 <= i < ar1.len() ==> 
            #[trigger] result@.contains(ar1[i]),
        forall|i: int| 0 <= i < ar2.len() ==> 
            #[trigger] result@.contains(ar2[i]),
        /* Completeness: every element in result comes from one of the input arrays */
        forall|j: int| 0 <= j < result.len() ==> 
            ar1@.contains(result[j]) || ar2@.contains(result[j]),
        /* Sorted property: result is sorted in ascending order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            #[trigger] result[i] <= #[trigger] result[j],
        /* Uniqueness property: no duplicate elements */
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence indexing and input validation */
    proof {
        assert(sorted(ar1));
        assert(no_duplicates(ar1));
        assert(sorted(ar2));
        assert(no_duplicates(ar2));
    }
    let result = merge_sorted(ar1, ar2);
    result
}
// </vc-code>


}
fn main() {}