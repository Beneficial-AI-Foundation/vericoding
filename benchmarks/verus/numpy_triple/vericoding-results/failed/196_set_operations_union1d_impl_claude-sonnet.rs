// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed insert_unique postconditions and loop invariants */
spec fn is_sorted(v: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn is_unique(v: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> v[i] != v[j]
}

// Helper function to insert an element into a sorted vector while maintaining sort order and uniqueness
fn insert_unique(mut v: Vec<i8>, elem: i8) -> (result: Vec<i8>)
    requires
        is_sorted(v@),
        is_unique(v@),
    ensures
        is_sorted(result@),
        is_unique(result@),
        result@.contains(elem),
        forall|x: i8| v@.contains(x) ==> result@.contains(x),
        forall|x: i8| result@.contains(x) ==> v@.contains(x) || x == elem,
{
    // Check if element already exists by iterating
    let mut found = false;
    let mut k = 0;
    while k < v.len()
        invariant
            0 <= k <= v.len(),
            !found ==> forall|i: int| 0 <= i < k ==> v[i] != elem,
            found ==> exists|i: int| 0 <= i < k && v[i] == elem,
        decreases v.len() - k
    {
        if v[k] == elem {
            found = true;
            break;
        }
        k += 1;
    }
    
    if found {
        return v;
    }
    
    let mut pos = 0;
    while pos < v.len()
        invariant
            0 <= pos <= v.len(),
            is_sorted(v@),
            is_unique(v@),
            forall|i: int| 0 <= i < pos ==> v[i] < elem,
            pos < v.len() ==> v[pos] >= elem,
        decreases v.len() - pos
    {
        if v[pos] >= elem {
            break;
        }
        pos += 1;
    }
    
    proof {
        // Prove that inserting at pos maintains sortedness
        if pos < v.len() {
            assert(v[pos] >= elem);
        }
        if pos > 0 {
            assert(v[pos - 1] < elem);
        }
    }
    
    v.insert(pos, elem);
    v
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
    /* code modified by LLM (iteration 5): simplified invariants to focus on core properties */
    let mut result = Vec::<i8>::new();
    
    // Insert all elements from ar1
    let mut i = 0;
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            is_sorted(result@),
            is_unique(result@),
            forall|k: int| 0 <= k < i ==> result@.contains(ar1[k]),
        decreases ar1.len() - i
    {
        result = insert_unique(result, ar1[i]);
        i += 1;
    }
    
    // Insert all elements from ar2
    let mut j = 0;
    while j < ar2.len()
        invariant
            0 <= j <= ar2.len(),
            is_sorted(result@),
            is_unique(result@),
            forall|k: int| 0 <= k < ar1.len() ==> result@.contains(ar1[k]),
            forall|k: int| 0 <= k < j ==> result@.contains(ar2[k]),
        decreases ar2.len() - j
    {
        result = insert_unique(result, ar2[j]);
        j += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}