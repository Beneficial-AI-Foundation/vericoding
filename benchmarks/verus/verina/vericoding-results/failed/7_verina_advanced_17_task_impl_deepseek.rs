// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unsupported is_empty() call and fixed proof functions */
proof fn lemma_insertion_preserves_multiset(v: Vec<i32>, idx: usize, value: i32) -> (result: Vec<i32>)
    ensures
        idx <= v.len(),
        result@.to_multiset() == v@.to_multiset().insert(value),
        result.len() == v.len() + 1
{
    let mut result = v.clone();
    result.insert(idx, value);
    result
}

proof fn lemma_sorted_invariant(v: Vec<i32>, i: int, j: int) -> (result: bool)
    ensures
        result == (
            forall|k: int| i <= k < j ==> v[k] <= v[k + 1]
        )
{
    if i >= j {
        true
    } else {
        v[i] <= v[i + 1] && lemma_sorted_invariant(v, i + 1, j)
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced unsupported is_empty() with len() check */
{
    let mut sorted = Vec::new();
    let mut original = l;
    
    while original.len() > 0
        invariant
            sorted@.to_multiset().add(original@.to_multiset()) == l@.to_multiset(),
            forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j],
            sorted.len() + original.len() == l.len()
        decreases original.len()
    {
        let elem = match original.pop() {
            Some(value) => value,
            None => break,
        };
        
        let mut pos: usize = 0;
        while pos < sorted.len()
            invariant
                0 <= pos <= sorted.len(),
                forall|i: int| 0 <= i < pos ==> sorted[i] <= elem,
                forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j]
            decreases sorted.len() - pos
        {
            if sorted[pos] > elem {
                break;
            }
            pos += 1;
        }
        
        sorted.insert(pos, elem);
    }
    
    sorted
}
// </vc-code>

}
fn main() {}