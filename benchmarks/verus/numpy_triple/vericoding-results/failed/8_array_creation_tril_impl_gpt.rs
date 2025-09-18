// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): triangular keep condition and arithmetic cast lemmas */
spec fn keep_cell(i: int, j: int, k: int) -> bool { i >= j - k }

/* helper modified by LLM (iteration 5): lemma for translating usize subtraction to int */
proof fn lemma_usize_sub_as_int(j: usize, kk: usize)
    requires
        kk <= j,
    ensures
        (j as int) - (kk as int) == (j - kk) as int
{ }

/* helper modified by LLM (iteration 5): lemma for translating usize subtraction to int (i - kn) */
proof fn lemma_usize_sub_as_int2(i: usize, kn: usize)
    requires
        kn <= i,
    ensures
        (i as int) - (kn as int) == (i - kn) as int
{ }

/* helper modified by LLM (iteration 5): non-negativity of usize when cast to int */
proof fn lemma_usize_nonneg(u: usize)
    ensures
        (u as int) >= 0
{ }
// </vc-helpers>

// <vc-spec>
fn tril(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == if i >= j - k { m[i][j] } else { 0.0 },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement tril without using 'int' in exec code; prove linkage to spec condition in proof blocks */
    let rows = m.len();
    let cols = m[0].len();
    let mut out: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            rows == m.len(),
            cols == m[0].len(),
            out.len() == i,
            out@.len() == i as int,
            m@.len() == rows as int,
            m@[0]@.len() == cols as int,
            forall|rr: int| 0 <= rr < m@.len() ==> #[trigger] m@[rr]@.len() == m@[0]@.len(),
            forall|ii: int| 0 <= ii < i as int ==> out@[ii]@.len() == cols as int,
            forall|ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < cols as int ==>
                    #[trigger] out@[ii]@[jj] == if ii >= jj - (k as int) { m@[ii]@[jj] } else { 0.0 },
        decreases rows - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                i < rows,
                j <= cols,
                row.len() == j,
                row@.len() == j as int,
                m@.len() == rows as int,
                m@[0]@.len() == cols as int,
                forall|rr: int| 0 <= rr < m@.len() ==> #[trigger] m@[rr]@.len() == m@[0]@.len(),
                0 <= (i as int) && (i as int) < (rows as int),
                m@[i as int]@.len() == cols as int,
                forall|jj: int| 0 <= jj < j as int ==> #[trigger] row@[jj] == if (i as int) >= jj - (k as int) { m@[i as int]@[jj] } else { 0.0 },
            decreases cols - j
        {
            proof {
                // Indexing safety for m[i][j]
                assert(i < rows);
                assert(0 <= i as int && (i as int) < (m.len() as int));
                assert(m[i].len() == m[0].len());
                assert(j < cols);
                assert(j < m[i].len());
            }
            if k >= 0 {
                let kk: usize = k as usize;
                if j >= kk {
                    let cond1: bool = (j - kk) <= i;
                    let val = if cond1 { m[i][j] } else { 0.0 };
                    row.push(val);
                    proof {
                        // Bridge exec cond1 with spec condition
                        // From j >= kk, we can translate subtraction under casts
                        assert(j >= kk);
                        lemma_usize_sub_as_int(j, kk);
                        // (k as int) equals (kk as int) since k >= 0
                        assert((k as int) == (kk as int));
                        // i >= j - k  <==>  (j - k) <= i
                        assert(((i as int) >= (j as int) - (k as int)) == (((j as int) - (k as int)) <= (i as int)));
                        // Replace j - k with (j - kk)
                        assert((((j as int) - (k as int)) <= (i as int)) == (((j - kk) as int) <= (i as int)));
                        // Now relate spec comparison to exec cond1
                        if cond1 {
                            assert(((j - kk) as int) <= (i as int));
                            assert((i as int) >= (j as int) - (k as int));
                        } else {
                            assert(!(((j - kk) as int) <= (i as int)));
                            assert(!((i as int) >= (j as int) - (k as int)));
                        }
                        assert(m@[i as int]@[j as int] == m[i][j]);
                        assert(row@[j as int] == val);
                    }
                } else {
                    // j < kk => j - k is negative, hence i >= j - k holds since i >= 0
                    let val = m[i][j];
                    row.push(val);
                    proof {
                        lemma_usize_nonneg(i);
                        assert(j < kk);
                        assert((k as int) == (kk as int));
                        // j < kk  =>  (j as int) - (k as int) < 0 <= i
                        assert((j as int) - (k as int) < 0);
                        assert((i as int) >= (j as int) - (k as int));
                        assert(m@[i as int]@[j as int] == m[i][j]);
                        assert(row@[j as int] == val);
                    }
                }
            } else {
                // k < 0
                let kn: usize = (-(k as i64)) as usize; // kn = -k as nonnegative
                if kn <= i {
                    let rhs: usize = i - kn;
                    let cond2: bool = j <= rhs;
                    let val = if cond2 { m[i][j] } else { 0.0 };
                    row.push(val);
                    proof {
                        lemma_usize_sub_as_int2(i, kn);
                        // kn corresponds to -(k as int)
                        assert((kn as int) == (-(k as int)));
                        // i >= j - k  <==>  j <= i + (-k)  <==>  j <= i - kn
                        assert(((i as int) >= (j as int) - (k as int)) == ((j as int) <= (i as int) + (-(k as int))));
                        assert(((j as int) <= (i as int) + (-(k as int))) == ((j as int) <= (i as int) - (kn as int)));
                        assert(((j as int) <= (i as int) - (kn as int)) == ((j as int) <= (rhs as int)));
                        if cond2 {
                            assert((j as int) <= (rhs as int));
                            assert((i as int) >= (j as int) - (k as int));
                        } else {
                            assert(!((j as int) <= (rhs as int)));
                            assert(!((i as int) >= (j as int) - (k as int)));
                        }
                        assert(m@[i as int]@[j as int] == m[i][j]);
                        assert(row@[j as int] == val);
                    }
                } else {
                    // kn > i => i >= j - k is false for all j >= 0
                    let val = 0.0;
                    row.push(val);
                    proof {
                        lemma_usize_nonneg(j);
                        assert((kn as int) > (i as int));
                        assert((j as int) + (kn as int) > (i as int));
                        assert((j as int) - (k as int) == (j as int) + (kn as int));
                        assert(!((i as int) >= (j as int) - (k as int)));
                        assert(row@[j as int] == val);
                    }
                }
            }
            j = j + 1;
        }
        // At loop exit, j == cols and row satisfies the property for all indices < cols by invariant
        out.push(row);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}