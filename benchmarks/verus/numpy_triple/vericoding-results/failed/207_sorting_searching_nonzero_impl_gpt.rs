// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified lemma to avoid assert_forall_by parsing issues */
proof fn lemma_usize_lt_implies_ne(x: usize, y: usize)
    requires
        x < y,
    ensures
        x != y,
{
}

// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement scan collecting nonzero indices with strong loop invariants; removed helper call */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> indices@[k] < i,
            forall|k: int| 0 <= k < indices.len() ==> a[indices@[k] as int] != 0.0f32,
            forall|k1: int, k2: int| 0 <= k1 < k2 < indices.len() ==> indices@[k1] < indices@[k2],
            forall|j: int| 0 <= j < i as int && a[j] != 0.0f32 ==> exists|k: int| 0 <= k < indices.len() && indices@[k] == j,
        decreases a.len() - i
    {
        let oi: usize = i;
        let old_len: usize = indices.len();
        let ghost old_seq: Seq<usize> = indices@;

        if a[oi] != 0.0f32 {
            indices.push(oi);
        }

        i = oi + 1;

        proof {
            let pushed = a[oi] != 0.0f32;
            if pushed {
                assert(indices@ == old_seq.push(oi));
            } else {
                assert(indices@ == old_seq);
            }

            assert_forall_by(|k: int| 0 <= k < indices.len() ==> indices@[k] < i) {
                requires 0 <= k < indices.len();
                if pushed {
                    let last: int = indices@.len() - 1;
                    if k == last {
                        assert(indices@[k] == oi);
                        assert(oi < i);
                    } else {
                        assert(k < old_seq.len());
                        assert(indices@[k] == old_seq[k]);
                        assert(old_seq[k] < oi);
                        assert(old_seq[k] < i);
                    }
                } else {
                    assert(k < old_seq.len());
                    assert(indices@[k] == old_seq[k]);
                    assert(old_seq[k] < oi);
                    assert(old_seq[k] < i);
                }
            };

            assert_forall_by(|k: int| 0 <= k < indices.len() ==> a[indices@[k] as int] != 0.0f32) {
                requires 0 <= k < indices.len();
                if pushed {
                    let last: int = indices@.len() - 1;
                    if k == last {
                        assert(indices@[k] == oi);
                        assert(a[oi as int] != 0.0f32);
                    } else {
                        assert(k < old_seq.len());
                        assert(indices@[k] == old_seq[k]);
                        assert(a[old_seq[k] as int] != 0.0f32);
                    }
                } else {
                    assert(k < old_seq.len());
                    assert(indices@[k] == old_seq[k]);
                    assert(a[old_seq[k] as int] != 0.0f32);
                }
            };

            assert_forall_by(|k1: int, k2: int| 0 <= k1 < k2 < indices.len() ==> indices@[k1] < indices@[k2]) {
                requires 0 <= k1 < k2 < indices.len();
                if pushed {
                    let last: int = indices@.len() - 1;
                    if k2 == last {
                        assert(k1 < old_seq.len());
                        assert(indices@[k1] == old_seq[k1]);
                        assert(old_seq[k1] < oi);
                        assert(indices@[k2] == oi);
                    } else {
                        assert(k1 < old_seq.len());
                        assert(k2 < old_seq.len());
                        assert(indices@[k1] == old_seq[k1]);
                        assert(indices@[k2] == old_seq[k2]);
                        assert(old_seq[k1] < old_seq[k2]);
                    }
                } else {
                    assert(k1 < old_seq.len());
                    assert(k2 < old_seq.len());
                    assert(indices@[k1] == old_seq[k1]);
                    assert(indices@[k2] == old_seq[k2]);
                    assert(old_seq[k1] < old_seq[k2]);
                }
            };

            assert_forall_by(|j: int| 0 <= j < i as int && a[j] != 0.0f32 ==> exists|k: int| 0 <= k < indices.len() && indices@[k] == j) {
                requires 0 <= j < i as int && a[j] != 0.0f32;
                if j < oi as int {
                    let ex = choose|k: int| 0 <= k < old_seq.len() && old_seq[k] == j;
                    if pushed {
                        assert(indices@ == old_seq.push(oi));
                    } else {
                        assert(indices@ == old_seq);
                    }
                    assert(0 <= ex < indices@.len());
                    assert(indices@[ex] == j);
                } else {
                    assert(j == oi as int);
                    assert(pushed);
                    let last: int = indices@.len() - 1;
                    assert(indices@[last] == oi);
                    assert(indices@[last] == j);
                }
            };
        }
    }
    indices
}

// </vc-code>

}
fn main() {}