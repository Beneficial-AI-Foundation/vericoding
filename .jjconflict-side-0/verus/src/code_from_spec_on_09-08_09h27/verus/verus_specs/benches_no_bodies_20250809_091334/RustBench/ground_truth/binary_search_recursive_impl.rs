use vstd::prelude::*;

verus! {

fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    decreases f - c + 1
{
    if c > f {
        // Search range is empty, return largest valid index before c
        c - 1
    } else {
        let mid = c + (f - c) / 2;
        if v[mid as usize] <= elem {
            // Element at mid is ≤ elem, search in upper half
            binary_search_recursive(v, elem, mid + 1, f)
        } else {
            // Element at mid is > elem, search in lower half
            binary_search_recursive(v, elem, c, mid - 1)
        }
    }
}

fn main() {}
}