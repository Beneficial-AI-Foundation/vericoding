// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to check if a vector is sorted
spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

/* helper modified by LLM (iteration 5): fixed old() usage with proper reference */
// Helper function to insert an element at the correct position
fn insert_sorted(mut sorted: Vec<i32>, element: i32) -> (result: Vec<i32>)
    requires is_sorted(sorted@),
    ensures is_sorted(result@),
            result@.to_multiset() == old(sorted@).to_multiset().insert(element),
{
    let mut pos = 0;
    while pos < sorted.len()
        invariant
            0 <= pos <= sorted.len(),
            is_sorted(sorted@),
            forall|k: int| 0 <= k < pos ==> sorted[k] <= element,
        decreases sorted.len() - pos
    {
        if sorted[pos] > element {
            break;
        }
        pos += 1;
    }
    sorted.insert(pos, element);
    sorted
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed old() usage issue */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            is_sorted(result@),
            result@.to_multiset() == l@.subrange(0, i as int).to_multiset(),
        decreases l.len() - i
    {
        result = insert_sorted(result, l[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}