use vstd::prelude::*;

verus! {

fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    // pre-conditions-start
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    // post-conditions-end
    decreases f - c + 1
{
    if c > f {
        return c - 1;
    }
    
    let mid = c + (f - c) / 2;
    
    if v[mid as usize] <= elem {
        binary_search_recursive(v, elem, mid + 1, f)
    } else {
        binary_search_recursive(v, elem, c, mid - 1)
    }
}

fn main() {}

/* code modified by LLM (iteration 2): Removed all text outside the verus block that was causing compilation errors */
// The implementation works as follows:
// - If v[mid] <= elem, we know the answer could be at mid or later, so we search in the right half [mid + 1, f]
// - If v[mid] > elem, we know the answer must be before mid, so we search in the left half [c, mid - 1]
//
// The key insight is that this maintains the invariants:
// - Elements before the current search range are <= elem  
// - Elements after the current search range are > elem
// - When we eliminate the left half, we extend the "<= elem" region
// - When we eliminate the right half, we extend the "> elem" region
//
// This correctly implements the binary search to find the rightmost position where elements are <= elem.

}