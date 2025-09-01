use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sorted_implies_property(v: &[i32], i: int, j: int, elem: i32)
    requires
        forall|x: int, y: int| 0 <= x < y < v.len() ==> v[x] <= v[y],
        0 <= i <= j < v.len(),
        v[j] <= elem,
    ensures
        forall|k: int| i <= k <= j ==> v[k] <= elem,
{
    assert(forall|k: int| i <= k <= j ==> v[k] <= v[j] <= elem);
}

proof fn sorted_implies_property_greater(v: &[i32], i: int, j: int, elem: i32)
    requires
        forall|x: int, y: int| 0 <= x < y < v.len() ==> v[x] <= v[y],
        0 <= i <= j < v.len(),
        v[i] > elem,
    ensures
        forall|k: int| i <= k <= j ==> v[k] > elem,
{
    assert(forall|k: int| i <= k <= j ==> v[i] <= v[k] && v[i] > elem);
}
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
        return f;
    }
    
    let mid = c + (f - c) / 2;
    
    if v[mid as usize] <= elem {
        proof {
            sorted_implies_property(v, c as int, mid as int, elem);
        }
        binary_search_recursive(v, elem, mid + 1, f)
    } else {
        proof {
            sorted_implies_property_greater(v, mid as int, f as int, elem);
        }
        binary_search_recursive(v, elem, c, mid - 1)
    }
}
// </vc-code>

fn main() {}
}