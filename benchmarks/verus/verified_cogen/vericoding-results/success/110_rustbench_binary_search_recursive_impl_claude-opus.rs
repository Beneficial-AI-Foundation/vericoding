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
    /* code modified by LLM (iteration 4): Fixed assertion by handling case when k is between c and mid */
    if c > f {
        return (f as isize);
    }
    let mid = c + (f - c) / 2;
    if v[mid as usize] <= elem {
        if mid < f {
            proof {
                assert forall|k: int| 0 <= k <= mid implies v@[k] <= elem by {
                    if k < c {
                        assert(v@[k] <= elem);
                    } else if k == mid {
                        assert(v@[mid as int] <= elem);
                    } else {
                        assert(c <= k < mid);
                        assert(v@[k] <= v@[mid as int]);
                        assert(v@[mid as int] <= elem);
                        assert(v@[k] <= elem);
                    }
                }
            }
            binary_search_recursive(v, elem, mid + 1, f)
        } else {
            return mid;
        }
    } else {
        proof {
            assert forall|k: int| mid <= k < v@.len() implies v@[k] > elem by {
                if k == mid {
                    assert(v@[mid as int] > elem);
                } else if k > f {
                    assert(v@[k] > elem);
                } else {
                    assert(mid < k <= f);
                    assert(v@[mid as int] > elem);
                    assert(v@[mid as int] <= v@[k]);
                    assert(v@[k] > elem);
                }
            }
        }
        binary_search_recursive(v, elem, c, mid - 1)
    }
}
// </vc-code>

}
fn main() {}