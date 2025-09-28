// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial check that last coefficient is non-zero */
fn check_nonzero(b: i8)
    requires
        b != 0,
{
}

/* helper modified by LLM (iteration 5): cast usize to int helper */
fn usize_to_int(u: usize) -> int
    ensures
        result == u as int,
{
    u as int
}
// </vc-helpers>

// <vc-spec>
fn polycompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            (if i + 1 == j && i < c.len() - 2 {
                result[i][j] as int == 1
            } else if i == c.len() - 2 {
                result[i][j] as int * c[c.len() - 1] as int == -c[j] as int
            } else {
                result[i][j] as int == 0
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct companion matrix using int loop counters and proper casts */
    let n: int = c.len() as int;
    let m: int = n - 1;

    check_nonzero(c[c.len() - 1]);

    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: int = 0;
    while i < m
        invariant
            0 <= i && i <= m,
            res.len() as int == i,
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: int = 0;
        while j < m
            invariant
                0 <= j && j <= m,
                row.len() as int == j,
            decreases m - j
        {
            if i + 1 == j && i < m - 1 {
                row.push(1i8);
            } else if i == m - 1 {
                let idx_j: usize = j as usize;
                let idx_m: usize = m as usize;
                let numerator: i16 = -(c[idx_j] as i16);
                let denom: i16 = c[idx_m] as i16;
                let q_i16: i16 = numerator / denom;
                let q: i8 = q_i16 as i8;
                row.push(q);
            } else {
                row.push(0i8);
            }
            j = j + 1;
        }
        res.push(row);
        i = i + 1;
    }

    // proof of postconditions
    proof {
        assert(res.len() as int == m);
        let mut ii: int = 0;
        while ii < m
            invariant
                0 <= ii && ii <= m,
            decreases m - ii
        {
            let ui: usize = ii as usize;
            assert(res[ui].len() as int == m);
            let mut jj: int = 0;
            while jj < m
                invariant
                    0 <= jj && jj <= m,
                decreases m - jj
            {
                let uj: usize = jj as usize;
                if ii + 1 == jj && ii < m - 1 {
                    assert(res[ui][uj] as int == 1);
                } else if ii == m - 1 {
                    let idx_m: usize = m as usize;
                    assert((res[ui][uj] as int) * (c[idx_m] as int) == -(c[uj] as int));
                } else {
                    assert(res[ui][uj] as int == 0);
                }
                jj = jj + 1;
            }
            ii = ii + 1;
        }
    }

    res
}
// </vc-code>


}
fn main() {}