// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn cond(i: usize, j: usize, k: i32) -> bool {
    (j as int) <= (i as int) + (k as int)
}

/* helper modified by LLM (iteration 2): named return to bind 'result' in ensures */
fn val_for(i: usize, j: usize, k: i32) -> (result: f64)
    ensures
        result == if cond(i, j, k) { 1.0 } else { 0.0 },
{
    if k >= 0 {
        let kuz: usize = k as usize;
        if j <= i {
            proof {
                assert(cond(i, j, k));
                assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 1.0);
            }
            1.0
        } else {
            let d: usize = j - i;
            if d <= kuz {
                proof {
                    assert((j as int) == (i as int) + (d as int));
                    assert((k as int) >= 0);
                    assert((d as int) <= (kuz as int));
                    assert((kuz as int) == (k as int));
                    assert((j as int) <= (i as int) + (k as int));
                    assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 1.0);
                }
                1.0
            } else {
                proof {
                    assert((j as int) == (i as int) + (d as int));
                    assert((k as int) >= 0);
                    assert((d as int) > (kuz as int));
                    assert((kuz as int) == (k as int));
                    assert(!((j as int) <= (i as int) + (k as int)));
                    assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 0.0);
                }
                0.0
            }
        }
    } else {
        let neg64: i64 = -(k as i64);
        let neg_us: usize = neg64 as usize;
        if i < neg_us {
            proof {
                assert((neg_us as int) == (-(k as int)));
                assert((i as int) < (-(k as int)));
                assert((i as int) + (k as int) < 0);
                assert(!((j as int) <= (i as int) + (k as int)));
                assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 0.0);
            }
            0.0
        } else {
            let upper: usize = i - neg_us;
            if j <= upper {
                proof {
                    assert((neg_us as int) == (-(k as int)));
                    assert((upper as int) == (i as int) - (neg_us as int));
                    assert((upper as int) == (i as int) + (k as int));
                    assert((j as int) <= (i as int) + (k as int));
                    assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 1.0);
                }
                1.0
            } else {
                proof {
                    assert((neg_us as int) == (-(k as int)));
                    assert((upper as int) == (i as int) + (k as int));
                    assert((j as int) > (upper as int));
                    assert(!((j as int) <= (i as int) + (k as int)));
                    assert((if cond(i, j, k) { 1.0 } else { 0.0 }) == 0.0);
                }
                0.0
            }
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
    /* code modified by LLM (iteration 2): construct matrix using nested loops and val_for, maintaining invariants */
    let mut res: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            0 <= i <= n,
            forall|ii: int| 0 <= ii < i ==> res@[ii].len() == m,
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < m ==>
                    res@[ii]@[jj] == if cond(ii as usize, jj as usize, k) { 1.0 } else { 0.0 },
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                row.len() == j,
                0 <= j <= m,
                forall|jj: int| 0 <= jj < j ==>
                    row@[jj] == if cond(i, jj as usize, k) { 1.0 } else { 0.0 },
            decreases m - j
        {
            let v = val_for(i, j, k);
            row.push(v);
            j = j + 1;
        }
        res.push(row);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}