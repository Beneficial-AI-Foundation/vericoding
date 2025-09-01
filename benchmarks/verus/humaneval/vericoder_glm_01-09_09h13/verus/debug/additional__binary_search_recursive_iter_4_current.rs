use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_binary_search_recursive_preserves_invariants(
    v: &[i32],
    elem: i32,
    c: isize,
    f: isize,
    mid: isize,
) {
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
        c <= mid <= f,
    ensures
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
        if v[mid as int] <= elem {
            forall|k: int| 0 <= k < (mid + 1) ==> v[k] <= elem,
            forall|k: int| f < k < v.len() ==> v[k] > elem,
        } else {
            forall|k: int| 0 <= k < c ==> v[k] <= elem,
            forall|k: int| mid < k < v.len() ==> v[k] > elem,
        }
{
    if v[mid as int] <= elem {
        assert(forall|k: int| 0 <= k < c ==> v[k] <= elem by {
            forall|k: int| 0 <= k < c
                ensures v[k] <= elem
            {
                assert(v[k] <= elem);
            }
        });
        assert(v[mid as int] <= elem);
        assert(forall|k: int| 0 <= k < (mid + 1) ==> v[k] <= elem by {
            forall|k: int| 0 <= k < (mid + 1)
                ensures v[k] <= elem
            {
                if k < mid {
                    assert(v[k] <= v[mid as int] by {
                        assert(0 <= k < mid < v.len());
                        let i = k;
                        let j = mid as int;
                        assert(0 <= i < j < v.len());
                        assert(v[i] <= v[j]);
                    });
                    assert(v[mid as int] <= elem);
                } else {
                    assert(v[mid as int] <= elem);
                }
            }
        });
    } else {
        assert(forall|k: int| f < k < v.len() ==> v[k] > elem by {
            forall|k: int| f < k < v.len()
                ensures v[k] > elem
            {
                assert(v[k] > elem);
            }
        });
        assert(v[mid as int] > elem);
        assert(forall|k: int| mid < k < v.len() ==> v[k] > elem by {
            forall|k: int| mid < k < v.len()
                ensures v[k] > elem
            {
                if k > f {
                    assert(v[k] > elem);
                } else {
                    assert(mid < k <= f < v.len());
                    assert(v[mid as int] <= v[k] by {
                        let i = mid as int;
                        let j = k;
                        assert(0 <= i < j < v.len());
                        assert(v[i] <= v[j]);
                    });
                    assert(v[mid as int] > elem);
                }
            }
        });
    }
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
        let bound = c - 1;
        assert(forall|u: int| 0 <= u <= bound ==> v[u] <= elem by {
            forall|u: int| 0 <= u <= bound
                ensures v[u] <= elem
            {
                assert(u < c);
                assert(v[u] <= elem);
            }
        });
        assert(forall|w: int| bound < w < v.len() ==> v[w] > elem by {
            forall|w: int| bound < w < v.len()
                ensures v[w] > elem
            {
                assert(w > bound);
                assert(bound == c - 1);
                assert(c > f);
                assert(w >= c);
                assert(w > f);
                assert(v[w] > elem);
            }
        });
        bound
    } else {
        let mid = (c + f) / 2;
        lemma_binary_search_recursive_preserves_invariants(v, elem, c, f, mid);

        if v[mid as int] <= elem {
            let result = binary_search_recursive(v, elem, mid + 1, f);
            result
        } else {
            let result = binary_search_recursive(v, elem, c, mid - 1);
            result
        }
    }
}
// </vc-code>

fn main() {}
}