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
    // impl-start
    if c > f {
        // This case handles an empty search space.
        // It implies that all elements up to `f` are <= elem, and all elements from `c` onwards are > elem.
        // If c > f, then the entire original range cannot contain elem.
        // The post-condition requires that `p` is the last index `u` for which `v[u] <= elem`.
        // If `v` contains `elem`, then `p` will be the last such index.
        // If `v` does not contain `elem`, then `p` should represent the last index for which `v[p] <= elem`.
        // Consider the original pre-conditions:
        // forall|k: int| 0 <= k < c ==> v[k] <= elem,
        // forall|k: int| f < k < v.len() ==> v[k] > elem,
        // If c > f, then we effectively have:
        // forall|k: int| 0 <= k < f + 1 ==> v[k] <= elem (since f+1 <= c)
        // forall|k: int| f < k < v.len() ==> v[k] > elem
        // This means `f` effectively becomes `p`.
        f
    } else {
        let mid = c + (f - c) / 2;
        let v_mid = v[mid as usize];

        if v_mid <= elem {
            // elem must be in the right half (including mid), or not present.
            // The new search space is [mid, f].
            // We need to maintain:
            // forall|k: int| 0 <= k < c' ==> v[k] <= elem
            // Here c' becomes mid + 1, so we need to ensure 0 <= k < mid + 1 ==> v[k] <= elem.
            // We know 0 <= k < c ==> v[k] <= elem (original pre-condition)
            // And for c <= k <= mid, if v[mid] <= elem, and v is sorted, then v[k] <= elem.
            // So, for 0 <= k <= mid, v[k] <= elem holds. Thus 0 <= k < mid + 1 ==> v[k] <= elem holds for the recursive call.
            //
            // And we need to maintain:
            // forall|k: int| f' < k < v.len() ==> v[k] > elem
            // Here f' remains f, which is okay.
            binary_search_recursive(v, elem, mid + 1, f)
        } else {
            // elem must be in the left half, or not present.
            // The new search space is [c, mid - 1].
            // We need to maintain:
            // forall|k: int| 0 <= k < c' ==> v[k] <= elem
            // Here c' remains c, which is okay.
            //
            // And we need to maintain:
            // forall|k: int| f' < k < v.len() ==> v[k] > elem
            // Here f' becomes mid - 1. So we need to ensure mid - 1 < k < v.len() ==> v[k] > elem.
            // We know f < k < v.len() ==> v[k] > elem (original pre-condition)
            // And for mid <= k <= f, if v[mid] > elem, and v is sorted, then v[k] > elem.
            // So, for mid <= k <= v.len() - 1, v[k] > elem holds. Specifically, for mid <= k < v.len(), v[k] > elem.
            // This means for mid - 1 < k < v.len(), v[k] > elem holds.
            binary_search_recursive(v, elem, c, mid - 1)
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}