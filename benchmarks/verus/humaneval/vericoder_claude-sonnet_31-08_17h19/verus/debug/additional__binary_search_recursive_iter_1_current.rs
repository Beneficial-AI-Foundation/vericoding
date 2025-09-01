use vstd::prelude::*;

verus! {

// <vc-helpers>

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
        return -1;
    }
    
    let mid = c + (f - c) / 2;
    
    if v[mid as usize] <= elem {
        assert(forall|k: int| 0 <= k <= mid ==> v[k] <= elem);
        binary_search_recursive(v, elem, mid + 1, f)
    } else {
        assert(forall|k: int| mid <= k < v.len() ==> v[k] > elem);
        binary_search_recursive(v, elem, c, mid - 1)
    }
}
// </vc-code>

fn main() {}
}