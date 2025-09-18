// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): index equality from sequence equality for f32 */
proof fn lemma_seq_index_from_equality_f32(s1: Seq<f32>, s2: Seq<f32>, j: int)
    requires
        0 <= j < s1.len(),
        s1 == s2,
    ensures
        s1[j] == s2[j]
{
    assert(s1.len() == s2.len());
    assert(0 <= j < s2.len());
    assert(s1[j] == s2[j]);
}

/* helper modified by LLM (iteration 5): existence witness k = j in a row */
proof fn lemma_exists_k_is_j_for_equal_row(row: Seq<f32>, j: int)
    requires
        0 <= j < row.len(),
    ensures
        exists|k: int| 0 <= k < row.len() && row[j] == row[k] && k == j
{
    assert(exists|k: int| 0 <= k < row.len() && row[j] == row[k] && k == j) by {
        let k = j;
        assert(0 <= k < row.len());
        assert(row[j] == row[k]);
        assert(k == j);
    }
}
// </vc-helpers>

// <vc-spec>
fn broadcast_to(v: Vec<f32>, m: usize) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures
        result.len() == m,

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> #[trigger] result[i][j] == v[j],

        forall|i: int| 0 <= i < m ==> #[trigger] result[i]@ == v@,

        forall|j: int, i1: int, i2: int| 0 <= j < v.len() && 0 <= i1 < m && 0 <= i2 < m ==> 
            #[trigger] result[i1][j] == #[trigger] result[i2][j],

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> exists|k: int| 0 <= k < v.len() && #[trigger] result[i][j] == v[k] && k == j,

        forall|i1: int, i2: int| 0 <= i1 < m && 0 <= i2 < m ==> #[trigger] result[i1]@ == #[trigger] result[i2]@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix int/usize index mismatches by using int indices in spec contexts and avoid converting lengths to usize */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            result.len() == i,
            i <= m,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k]@ == v@,
        decreases (m as int) - (i as int)
    {
        let row = v.clone();
        result.push(row.clone());
        i = i + 1;

        proof {
            let last_idx: int = result.len() - 1;
            assert(0 <= last_idx < result.len());
            assert(result[last_idx]@ == row@);
            assert(row@ == v@);
            assert forall|k: int| 0 <= k < result.len() implies #[trigger] result[k]@ == v@ by {
                if 0 <= k < result.len() {
                    if k == last_idx {
                        assert(result[k]@ == row@);
                        assert(row@ == v@);
                    } else {
                        assert(0 <= k < last_idx);
                        assert(result[k]@ == v@);
                    }
                }
            };
        }
    }

    proof {
        assert(result.len() == m);

        assert forall|i: int| 0 <= i < m implies #[trigger] result[i]@ == v@ by {
            if 0 <= i < m {
                assert(result[i]@ == v@);
            }
        };

        assert forall|i: int, j: int|
            0 <= i < m && 0 <= j < v.len()
            implies #[trigger] result[i][j] == v[j]
        by {
            if 0 <= i < m && 0 <= j < v.len() {
                assert(result[i]@ == v@);
                assert(result[i]@.len() == v@.len());
                assert(0 <= j < result[i]@.len());
                lemma_seq_index_from_equality_f32(result[i]@, v@, j);
            }
        };

        assert forall|j: int, i1: int, i2: int|
            0 <= j < v.len() && 0 <= i1 < m && 0 <= i2 < m
            implies #[trigger] result[i1][j] == #[trigger] result[i2][j]
        by {
            if 0 <= j < v.len() && 0 <= i1 < m && 0 <= i2 < m {
                assert(result[i1]@ == v@);
                assert(result[i2]@ == v@);
                assert(0 <= j < result[i1]@.len());
                assert(0 <= j < result[i2]@.len());
                lemma_seq_index_from_equality_f32(result[i1]@, v@, j);
                lemma_seq_index_from_equality_f32(result[i2]@, v@, j);
            }
        };

        assert forall|i: int, j: int|
            0 <= i < m && 0 <= j < v.len()
            implies exists|k: int| 0 <= k < v.len() && #[trigger] result[i][j] == v[k] && k == j
        by {
            if 0 <= i < m && 0 <= j < v.len() {
                assert(result[i]@ == v@);
                assert(0 <= j < result[i]@.len());
                lemma_seq_index_from_equality_f32(result[i]@, v@, j);
                assert(exists|k: int| 0 <= k < v.len() && result[i][j] == v[k] && k == j) by {
                    let k = j;
                    assert(0 <= k < v.len());
                    assert(result[i][j] == v[j]);
                    assert(k == j);
                }
            }
        };

        assert forall|i1: int, i2: int|
            0 <= i1 < m && 0 <= i2 < m
            implies #[trigger] result[i1]@ == #[trigger] result[i2]@
        by {
            if 0 <= i1 < m && 0 <= i2 < m {
                assert(result[i1]@ == v@);
                assert(result[i2]@ == v@);
            }
        };
    }

    result
}
// </vc-code>

}
fn main() {}