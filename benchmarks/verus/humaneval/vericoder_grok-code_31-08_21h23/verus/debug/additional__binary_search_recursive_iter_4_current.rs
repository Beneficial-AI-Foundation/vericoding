use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed, but we need to fix types for indexing
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
        let p: isize = if c == 0 {
            -1
        } else {
            c - 1
        };
        proof {
            assert(forall|u: int| #![trigger(v@[u])] 0 <= u <= p ==> v@[u] <= elem);
            assert(-1 <= p < v.len() as int);
            if p == -1 {
                assert(c == 0);
                assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
                assert(forall|w: int| #![trigger(v@[w])] p < w < v.len() ==> v@[w] > elem);
            } else {
                assert(c > 0);
                assert(p == c - 1);
                assert(f == c - 1);
                assert(forall|u: int| #![trigger(v@[u])] 0 <= u <= p ==> v@[u] <= elem);
                assert(forall|k: int| #![trigger(v@[k])] 0 <= k < c ==> v@[k] <= elem);
                assert(forall|w: int| #![trigger(v@[w])] p < w < v.len() ==> v@[w] > elem);
                assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
            }
        }
        p
    } else {
        let mid = c + (f - c) / 2;
        let mid_usize = mid as usize;
        assert(0 <= mid < (v.len() as isize));
        assert(mid_usize < v.len());
        let elem_at_mid = v[mid_usize];
        proof {
            assert(elem_at_mid == v@[mid as int]);
        }
        if elem_at_mid <= elem {
            // Recurse right
            assert(forall|k: int| #![trigger(v@[k])] 0 <= k < c ==> v@[k] <= elem);
            assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
            assert(forall|k: int| #![trigger(v@[k])] 0 <= k < mid ==> v@[k] <= elem) by {
                if mid == c {
                    assert(forall|k: int| #![trigger(v@[k])] 0 <= k < mid && k < c ==> v@[k] <= elem);
                } else {
                    assert(forall|k: int| #![trigger(v@[k])] 0 <= k < c ==> v@[k] <= elem);
                    assert(forall|k: int| #![trigger(v@[k])] c <= k < mid ==> v@[k] <= v@[mid as int] <= elem);
                }
            };
            assert(forall|k: int| #![trigger(v@[k])] (mid - 1) < k < v.len() ==> v@[k] > elem) by {
                assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
            };
            assert(mid <= f + 1 <= (v.len() as isize));
            binary_search_recursive(v, elem, mid, f)
        } else {
            // Recurse left
            assert(forall|k: int| #![trigger(v@[k])] 0 <= k < c ==> v@[k] <= elem);
            assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
            proof {
                assert(v@[mid as int] > elem);
                assert(forall|i: int| #![trigger(v@[i])] mid <= i < v.len() ==> v@[i] >= v@[mid as int] > elem);
            }
            if mid - 1 >= -1 {
                assert(c <= (mid - 1) + 1);
                assert(forall|k: int| #![trigger(v@[k])] 0 <= k < c ==> v@[k] <= elem);
                assert(forall|k: int| #![trigger(v@[k])] (mid - 1) < k < v.len() ==> v@[k] > elem) by {
                    assert(v@[mid as int] > elem);
                    assert(forall|i: int| #![trigger(v@[i])] mid <= i < v.len() ==> v@[i] >= v@[mid as int] > elem);
                    assert(forall|k: int| #![trigger(v@[k])] f < k < v.len() ==> v@[k] > elem);
                };
            } else {
                assert(mid - 1 == -1);
                assert(f < (v.len() as isize));
                assert(forall|k: int| #![trigger(v@[k])] (mid - 1) < k < v.len() ==> v@[k] > elem);
            }
            binary_search_recursive(v, elem, c, mid - 1)
        }
    }
}
// </vc-code>

fn main() {}
}