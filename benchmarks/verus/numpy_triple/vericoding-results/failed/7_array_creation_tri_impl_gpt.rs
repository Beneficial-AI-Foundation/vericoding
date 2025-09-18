// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable/spec condition and equivalence lemma for triangular matrix */
spec fn cond_spec(i: int, j: int, k: int) -> bool { j <= i + k }

/* helper modified by LLM (iteration 5): executable condition computation matching the spec condition */
fn cond_exec(i: usize, j: usize, k: i32) -> bool {
    if k >= 0 {
        j <= i + (k as usize)
    } else {
        let nk: usize = (-k) as usize;
        if nk > i { false } else { j <= i - nk }
    }
}

/* helper modified by LLM (iteration 5): lemma proving equivalence of exec/spec conditions */
proof fn lemma_cond_equiv(i: usize, j: usize, k: i32)
    ensures cond_exec(i, j, k) == cond_spec(i as int, j as int, k as int)
{
    if k >= 0 {
        let t: usize = i + (k as usize);
        assert(cond_exec(i, j, k) == (j <= t));
        assert((k as int) == ((k as usize) as int));
        assert((t as int) == (i as int + k as int));
        assert((j <= t) <==> ((j as int) <= (t as int)));
    } else {
        let nk: usize = (-k) as usize;
        if nk > i {
            assert(cond_exec(i, j, k) == false);
            assert((nk as int) == (-(k as int)));
            assert(i as int < nk as int);
            assert(i as int + k as int == i as int - nk as int);
            assert(i as int - nk as int < 0);
            assert(0 <= j as int);
            assert(!((j as int) <= (i as int + k as int)));
        } else {
            let t: usize = i - nk;
            assert(cond_exec(i, j, k) == (j <= t));
            assert((nk as int) == (-(k as int)));
            assert((t as int) == (i as int - nk as int));
            assert((i as int + k as int) == (t as int));
            assert((j <= t) <==> ((j as int) <= (t as int)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement exec condition with lemma equivalence and corrected invariants */
    let mut res: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i as int && i as int <= n as int
        invariant res@.len() == i as int
        invariant res.len() == i
        invariant forall|ii: int| 0 <= ii < res@.len() ==> res@[ii]@.len() == m as int
        invariant forall|ii: int, jj: int|
            0 <= ii < res@.len() && 0 <= jj < m as int ==> res@[ii]@[jj] == if cond_spec(ii, jj, k as int) { 1.0 } else { 0.0 }
        decreases n as int - i as int
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant 0 <= j as int && j as int <= m as int
            invariant row@.len() == j as int
            invariant forall|jj: int| 0 <= jj < row@.len() ==> row@[jj] == if cond_spec(i as int, jj, k as int) { 1.0 } else { 0.0 }
            decreases m as int - j as int
        {
            let b: bool = cond_exec(i, j, k);
            let val: f64 = if b { 1.0 } else { 0.0 };
            row.push(val);
            proof {
                lemma_cond_equiv(i, j, k);
                // From push semantics, the new element equals `val`, and `val` matches the spec condition
                assert((row@.len() - 1) as int == j as int);
                assert(row@[(j as int)] == (if cond_spec(i as int, j as int, k as int) { 1.0 } else { 0.0 }));
            }
            j += 1;
        }
        res.push(row);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}