use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    if c > f {
        // Empty range - all elements before c are <= elem
        // Return c - 1 (which could be -1 if c == 0)
        return (c - 1) as isize;
    }
    
    let mid: usize = (c + f) / 2;
    
    // Prove mid is in bounds
    assert(c <= mid);
    assert(mid <= f);
    assert(mid < v.len());
    
    if v[mid as usize] <= elem {
        // All elements up to mid are <= elem
        // Need to search the right half [mid+1, f]
        
        // Prove invariants for recursive call
        assert(forall|k: int| 0 <= k <= mid ==> v[k] <= elem) by {
            assert(forall|k: int| 0 <= k < c ==> v[k] <= elem);
            assert(forall|k: int| c <= k <= mid ==> v[k] <= v[mid as int]);
            assert(v[mid as int] <= elem);
        }
        
        binary_search_recursive(v, elem, (mid + 1) as isize, f)
    } else {
        // v[mid] > elem
        // All elements from mid onwards are > elem
        // Need to search the left half [c, mid-1]
        
        // Prove invariants for recursive call
        assert(forall|k: int| mid <= k < v.len() ==> v[k] > elem) by {
            assert(v[mid as int] > elem);
            assert(forall|k: int| mid <= k <= f ==> v[mid as int] <= v[k]);
            assert(forall|k: int| f < k < v.len() ==> v[k] > elem);
        }
        
        binary_search_recursive(v, elem, c, (mid - 1) as isize)
    }
}
// </vc-code>

fn main() {}
}