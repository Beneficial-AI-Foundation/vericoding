// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): safe reverse index computation and bound proof */
fn compute_rev_idx(len: usize, j: usize) -> (res: usize)
    requires
        len > 0,
        j < len,
    ensures
        res < len,
        res as int == len as int - 1 - j as int
{
    assert(j + 1 <= len);
    let r = len - 1 - j;
    proof {
        assert(r as int + j as int + 1 == len as int);
        assert(r as int == len as int - 1 - j as int);
    }
    assert(r < len);
    r
}
// </vc-helpers>

// <vc-spec>
fn fliplr(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[i].len(),
        forall|i: int, j: int| #![trigger result[i][j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==>
            result[i][j] == m[i][(m[i].len() - 1 - j as usize) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): ensured index bounds when reading from rows and strengthened assertions */
    let n = m.len();
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            m.len() == n,
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> result[k].len() == m[k].len(),
            forall|k: int, j: int|
                0 <= k && k < i as int && 0 <= j && j < result[k].len() as int ==>
                    result[k][j] == m[k][(m[k].len() - 1 - j as usize) as int]
        decreases n as int - i as int
    {
        let row = &m[i];
        let rl: usize = row.len();
        // From precondition: each row has len() > 0
        proof {
            assert(0 <= i as int && i as int < m.len() as int);
            assert(m[i as int].len() > 0);
        }
        assert(rl == row.len());
        assert(rl > 0);

        let mut rev_row: Vec<f32> = Vec::new();

        let mut j: usize = 0;
        while j < rl
            invariant
                rev_row.len() == j,
                j <= rl,
                forall|k: int| 0 <= k && k < rev_row.len() as int ==>
                    rev_row[k] == row[(rl - 1 - k as usize) as int]
            decreases rl as int - j as int
        {
            assert(j < rl);
            let idx = compute_rev_idx(rl, j);
            assert(idx < rl);
            assert(row.len() == rl);
            assert(idx < row.len());
            let val = row[idx];
            rev_row.push(val);
            j += 1;
        }

        // After inner loop: rev_row has length rl and mirrors row
        assert(rev_row.len() == rl);
        assert(m[i as int].len() == row.len());
        assert(rl == m[i as int].len());

        result.push(rev_row);
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}