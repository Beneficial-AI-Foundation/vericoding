// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    if c > f {
        f
    } else {
        let m = c + (f - c) / 2;
        if v[m as usize] <= elem {
            binary_search_recursive(v, elem, m + 1, f)
        } else {
            binary_search_recursive(v, elem, c, m - 1)
        }
    }
}
// </vc-code>

}
fn main() {}