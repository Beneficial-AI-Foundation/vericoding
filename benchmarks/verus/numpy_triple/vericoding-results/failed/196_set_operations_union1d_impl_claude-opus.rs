// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_contains_all(seq: Seq<i8>, other: Seq<i8>) -> bool {
    forall|i: int| 0 <= i < other.len() ==> seq.contains(other[i])
}

spec fn seq_sorted(seq: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

spec fn seq_no_duplicates(seq: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < seq.len() && 0 <= j < seq.len() && i != j ==> seq[i] != seq[j]
}

/* helper modified by LLM (iteration 4): Fixed postcondition preservation and added assertions for verification */
fn insert_sorted_unique(v: &mut Vec<i8>, elem: i8)
    requires
        seq_sorted(old(v)@),
        seq_no_duplicates(old(v)@),
    ensures
        v@.contains(elem),
        seq_sorted(v@),
        seq_no_duplicates(v@),
        forall|x: i8| old(v)@.contains(x) ==> v@.contains(x),
        forall|x: i8| v@.contains(x) ==> (old(v)@.contains(x) || x == elem),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            seq_sorted(v@),
            seq_no_duplicates(v@),
            forall|j: int| 0 <= j < i ==> v[j] < elem,
            v@ == old(v)@,
        decreases v.len() - i
    {
        if v[i] == elem {
            // Element already exists, no need to insert
            assert(v@.contains(elem));
            assert(forall|x: i8| old(v)@.contains(x) ==> v@.contains(x));
            return;
        } else if v[i] > elem {
            // Found insertion point
            v.insert(i, elem);
            assert(v@[i] == elem);
            assert(v@.contains(elem));
            assert(forall|x: i8| old(v)@.contains(x) ==> v@.contains(x));
            return;
        }
        i += 1;
    }
    // Insert at end
    v.push(elem);
    assert(v@[v.len() - 1] == elem);
    assert(v@.contains(elem));
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
    /* code modified by LLM (iteration 4): No changes needed in main code */
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            seq_sorted(result@),
            seq_no_duplicates(result@),
            forall|j: int| 0 <= j < i ==> result@.contains(ar1[j]),
            forall|x: i8| result@.contains(x) ==> exists|j: int| 0 <= j < i && ar1[j] == x,
        decreases ar1.len() - i
    {
        insert_sorted_unique(&mut result, ar1[i]);
        i += 1;
    }
    
    let mut j = 0;
    while j < ar2.len()
        invariant
            0 <= j <= ar2.len(),
            seq_sorted(result@),
            seq_no_duplicates(result@),
            seq_contains_all(result@, ar1@),
            forall|k: int| 0 <= k < j ==> result@.contains(ar2[k]),
            forall|x: i8| result@.contains(x) ==> ar1@.contains(x) || exists|k: int| 0 <= k < j && ar2[k] == x,
        decreases ar2.len() - j
    {
        insert_sorted_unique(&mut result, ar2[j]);
        j += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}