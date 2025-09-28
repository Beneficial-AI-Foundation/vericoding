// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix ==> usage and adapt to Vec inner rows */
proof fn lemma_symmetry_from_offdiag_zero(m: Seq<Vec<f32>>, n: int)
    requires
        0 <= n,
        m.len() == n,
        forall|i: int| 0 <= i < n ==> m[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> m[i][j] == 0.0f32,
    ensures
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> m[i][j] == m[j][i],
{
    assert forall |i: int, j: int|
        0 <= i < n && 0 <= j < n ==> m[i][j] == m[j][i]
    by
    {
        assert(0 <= i < n);
        assert(0 <= j < n);
        assert(m.len() == n);
        assert(0 <= i < m.len());
        assert(0 <= j < m.len());
        assert(m[i].len() == n);
        assert(m[j].len() == n);
        assert(0 <= j < m[i].len());
        assert(0 <= i < m[j].len());
        if i == j {
            assert(m[i][j] == m[j][i]);
        } else {
            assert(m[i][j] == 0.0f32);
            assert(m[j][i] == 0.0f32);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn diag(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures 
        result.len() == v.len(),
        forall|i: int| 0 <= i < v@.len() ==> result@[i].len() == v@.len(),
        /* Elements on the main diagonal are from v */
        forall|i: int| 0 <= i < v@.len() ==> result@[i][i] == v@[i],
        /* All off-diagonal elements are zero */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
        /* Diagonal matrix property - non-zero elements only on diagonal */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && result@[i][j] != 0.0f32 ==> i == j,
        /* The resulting matrix is symmetric */
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> result@[i][j] == result@[j][i],
        /* Each row has exactly one non-zero element at position i (unless v[i] = 0) */
        forall|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> {
            result@[i][i] != 0.0f32 && 
            forall|j: int| 0 <= j < v@.len() && j != i ==> result@[i][j] == 0.0f32
        },
        /* Each column has exactly one non-zero element at position j (unless v[j] = 0) */
        forall|j: int| 0 <= j < v@.len() && v@[j] != 0.0f32 ==> {
            result@[j][j] != 0.0f32 && 
            forall|i: int| 0 <= i < v@.len() && i != j ==> result@[i][j] == 0.0f32
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected ==> usage and completed diagonal construction with proofs */
    let n: usize = v.len();
    let n_int: int = n as int;
    proof { assert(v@.len() == n_int); }

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n_int,
            v@.len() == n_int,
            result@.len() == i as int,
            forall|p: int| 0 <= p < i as int ==> result@[p].len() == n_int,
            forall|p: int| 0 <= p < i as int ==> result@[p][p] == v@[p],
            forall|p: int, j: int| 0 <= p < i as int && 0 <= j < n_int && j != p ==> result@[p][j] == 0.0f32,
        decreases n_int - i as int
    {
        assert(i < n);
        let vi = v[i];

        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j as int <= n_int,
                row@.len() == j as int,
                forall|k: int| 0 <= k < j as int ==> row@[k] == if k == i as int { vi } else { 0.0f32 },
            decreases n_int - j as int
        {
            if j == i {
                row.push(vi);
            } else {
                row.push(0.0f32);
            }
            proof {
                assert(0 <= j as int < n_int);
                assert(row@[j as int] == if j as int == i as int { vi } else { 0.0f32 });
            }
            j = j + 1;
        }
        proof {
            assert(row@.len() == n_int);
            assert(forall|k: int| 0 <= k < n_int ==> row@[k] == if k == i as int { vi } else { 0.0f32 });
        }
        result.push(row);
        i = i + 1;
    }

    proof {
        assert(result@.len() == n_int);
        assert(forall|p: int| 0 <= p < n_int ==> result@[p].len() == n_int);
        assert(forall|p: int| 0 <= p < n_int ==> result@[p][p] == v@[p]);
        assert(forall|p: int, j: int| 0 <= p < n_int && 0 <= j < n_int && j != p ==> result@[p][j] == 0.0f32);

        assert forall |i2: int, j2: int|
            0 <= i2 < n_int && 0 <= j2 < n_int ==> (result@[i2][j2] != 0.0f32) ==> (i2 == j2)
        by
        {
            assert(0 <= i2 < n_int);
            assert(0 <= j2 < n_int);
            if i2 != j2 {
                assert(result@[i2][j2] == 0.0f32);
            }
        }

        lemma_symmetry_from_offdiag_zero(result@, n_int);

        assert forall |ii: int|
            0 <= ii < n_int && v@[ii] != 0.0f32 ==> { result@[ii][ii] != 0.0f32 && (forall |jj: int| 0 <= jj < n_int && jj != ii ==> result@[ii][jj] == 0.0f32) }
        by
        {
            assert(0 <= ii < n_int);
            assert(result@[ii][ii] == v@[ii]);
            assert(result@[ii][ii] != 0.0f32);
            assert(forall|jj: int| 0 <= jj < n_int && jj != ii ==> result@[ii][jj] == 0.0f32);
        }

        assert forall |jj: int|
            0 <= jj < n_int && v@[jj] != 0.0f32 ==> { result@[jj][jj] != 0.0f32 && (forall |ii: int| 0 <= ii < n_int && ii != jj ==> result@[ii][jj] == 0.0f32) }
        by
        {
            assert(0 <= jj < n_int);
            assert(result@[jj][jj] == v@[jj]);
            assert(result@[jj][jj] != 0.0f32);
            assert(forall|ii: int| 0 <= ii < n_int && ii != jj ==> result@[ii][jj] == 0.0f32);
        }
    }

    result
}
// </vc-code>


}
fn main() {}