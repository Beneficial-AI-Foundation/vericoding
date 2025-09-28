// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_unique(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

/* helper modified by LLM (iteration 2): added decreases clause to fix termination check */
fn insert_unique_sorted(v: Vec<i8>, x: i8) -> (res: Vec<i8>)
    requires
        is_sorted_unique(v@),
    ensures
        is_sorted_unique(res@),
        res@.to_set() == v@.to_set().insert(x),
{
    let mut insertion_idx: usize = 0;
    while insertion_idx < v.len()
        invariant
            insertion_idx <= v.len(),
            is_sorted_unique(v@),
            forall|k: int| 0 <= k < insertion_idx ==> v[k] < x,
        decreases v.len() - insertion_idx
    {
        if v[insertion_idx] == x {
            return v;
        }
        if v[insertion_idx] > x {
            break;
        }
        insertion_idx = insertion_idx + 1;
    }
    let mut res = v;
    res.insert(insertion_idx, x);
    res
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
    /* code modified by LLM (iteration 2): added decreases clauses to loops */
    let mut result = Vec::new();

    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            i <= ar1.len(),
            is_sorted_unique(result@),
            result@.to_set() == ar1@.subrange(0, i as int).to_set(),
        decreases ar1.len() - i
    {
        result = insert_unique_sorted(result, ar1[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < ar2.len()
        invariant
            j <= ar2.len(),
            is_sorted_unique(result@),
            result@.to_set() == ar1@.to_set().union(ar2@.subrange(0, j as int).to_set()),
        decreases ar2.len() - j
    {
        result = insert_unique_sorted(result, ar2[j]);
        j = j + 1;
    }

    result
}
// </vc-code>


}
fn main() {}