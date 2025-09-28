// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): replaced uses of implies(...) with ==> and clarified case split for push index */
proof fn lemma_push_preserves_strict_increasing(v: Seq<usize>, x: usize)
    requires
        forall|p: int, q: int| 0 <= p < v.len() && 0 <= q < v.len() && p < q ==> (v[p] as int) < (v[q] as int),
        forall|t: int| 0 <= t < v.len() ==> (v[t] as int) < (x as int),
    ensures
        forall|p: int, q: int| 0 <= p < v.len() + 1 && 0 <= q < v.len() + 1 && p < q ==> ((v.push(x)[p] as int) < (v.push(x)[q] as int)),
{
    assert forall|p: int, q: int|
        0 <= p < v.len() + 1 && 0 <= q < v.len() + 1 && p < q ==> (v.push(x)[p] as int) < (v.push(x)[q] as int)
    by {
        if q < v.len() {
            assert(0 <= p);
            assert(0 <= q);
            assert(p < q);
            assert(q < v.len());
            assert(p < v.len()) by { assert(p < q); assert(q < v.len()); }
            assert((v[p] as int) < (v[q] as int));
            assert(v.push(x)[p] == v[p]);
            assert(v.push(x)[q] == v[q]);
        } else {
            assert(!(q < v.len()));
            assert(q < v.len() + 1);
            assert(q == v.len());
            assert(0 <= p);
            assert(p < q);
            assert(p < v.len()) by { assert(p < q); assert(q == v.len()); }
            assert(v.push(x)[p] == v[p]);
            assert(v.push(x)[q] == x);
            assert((v[p] as int) < (x as int));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices@.len() ==> (#[trigger] indices@[i] as int) < a@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> a@[indices@[i] as int] != 0.0,
        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == i,
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices@[i] != indices@[j],
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && (indices@[i] as int) < (indices@[j] as int) ==> i < j,
        (indices@.len() == 0) == (forall|i: int| 0 <= i < a@.len() ==> a@[i] == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced implies(...) with ==> and kept loop invariants; implemented verified argwhere */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            forall|t: int| 0 <= t < indices@.len() ==> (#[trigger] (indices@[t] as int)) < i as int,
            forall|t: int| 0 <= t < indices@.len() ==> a@[indices@[t] as int] != 0.0,
            forall|k: int| 0 <= k < i as int && a@[k] != 0.0 ==> exists|t: int| 0 <= t < indices@.len() && indices@[t] as int == k,
            forall|p: int, q: int| 0 <= p < indices@.len() && 0 <= q < indices@.len() && p < q ==> ((indices@[p] as int) < (indices@[q] as int)),
        decreases (a.len() as int) - (i as int)
    {
        let oi: usize = i;
        let old_len: int = indices@.len();
        if a[i] != 0.0 {
            proof { lemma_push_preserves_strict_increasing(indices@, i); }
            indices.push(i);
            proof {
                assert(indices@.len() == old_len + 1);
                assert forall|t: int|
                    0 <= t < indices@.len()
                    ==> a@[indices@[t] as int] != 0.0
                by {
                    if t < old_len {
                        // Previously recorded index; property held by invariant
                    } else {
                        assert(t == old_len);
                        assert(indices@[t] as int == oi as int);
                        assert(a@[oi as int] != 0.0);
                    }
                }
            }
        }
        i = i + 1;
        proof {
            let new_i: int = i as int;
            let oi_int: int = oi as int;
            assert(new_i == oi_int + 1);
            assert(new_i <= a@.len());
            assert forall|k: int|
                0 <= k < new_i && a@[k] != 0.0
                ==> exists|t: int| 0 <= t < indices@.len() && indices@[t] as int == k
            by {
                if k < oi_int {
                    // Already covered by the invariant from previous iteration; witness still valid
                } else {
                    assert(k == oi_int);
                    if a@[oi_int] != 0.0 {
                        let t2: int = indices@.len() - 1;
                        assert(0 <= t2 && t2 < indices@.len());
                        assert(indices@[t2] as int == oi_int);
                    } else {
                        // antecedent requires a@[k] != 0.0, so this branch cannot occur
                    }
                }
            }
        }
    }
    proof {
        assert(i as int == a@.len());
        assert(forall|t: int| 0 <= t < indices@.len() ==> (indices@[t] as int) < a@.len());
        assert(forall|t: int| 0 <= t < indices@.len() ==> a@[indices@[t] as int] != 0.0);
        assert(forall|k: int| 0 <= k < a@.len() && a@[k] != 0.0 ==> exists|t: int| 0 <= t < indices@.len() && indices@[t] as int == k);
        assert(forall|p: int, q: int|
            0 <= p < indices@.len() && 0 <= q < indices@.len() && p != q
            ==> indices@[p] != indices@[q])
        by {
            assert forall|p: int, q: int|
                0 <= p < indices@.len() && 0 <= q < indices@.len() && p != q
                ==> indices@[p] != indices@[q]
            by {
                if p < q {
                    assert((indices@[p] as int) < (indices@[q] as int));
                } else {
                    assert(q < p);
                    assert((indices@[q] as int) < (indices@[p] as int));
                }
            }
        }
        assert(forall|p: int, q: int|
            0 <= p < indices@.len() && 0 <= q < indices@.len() && (indices@[p] as int) < (indices@[q] as int)
            ==> p < q)
        by {
            assert forall|p: int, q: int|
                0 <= p < indices@.len() && 0 <= q < indices@.len() && (indices@[p] as int) < (indices@[q] as int)
                ==> p < q
            by {
                if !(p < q) {
                    if p == q {
                        assert(!((indices@[p] as int) < (indices@[q] as int)));
                    } else {
                        assert(q < p);
                        assert((indices@[q] as int) < (indices@[p] as int));
                        assert(!((indices@[p] as int) < (indices@[q] as int)));
                    }
                }
            }
        }
        assert((indices@.len() == 0) ==> (forall|k: int| 0 <= k < a@.len() ==> a@[k] == 0.0))
        by {
            assert forall|k: int|
                0 <= k < a@.len()
                ==> a@[k] == 0.0
            by {
                if a@[k] != 0.0 {
                    assert(exists|t: int| 0 <= t < indices@.len() && indices@[t] as int == k);
                }
            }
        }
        assert((forall|k: int| 0 <= k < a@.len() ==> a@[k] == 0.0) ==> (indices@.len() == 0))
        by {
            if indices@.len() != 0 {
                let t: int = indices@.len() - 1;
                assert(0 <= t && t < indices@.len());
                let kk: int = indices@[t] as int;
                assert(0 <= kk && kk < a@.len());
                assert(a@[kk] != 0.0);
            }
        }
    }
    indices
}
// </vc-code>

}
fn main() {}