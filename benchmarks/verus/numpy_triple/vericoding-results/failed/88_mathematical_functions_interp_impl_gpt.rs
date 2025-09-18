// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): preserve boundary behavior; require either increasing bounds or equal function values and prove implications across branches */
fn select_value(x: i32, xp0: i32, xplast: i32, fp0: i32, fplast: i32) -> (result: i32)
    requires
        xp0 < xplast || fp0 == fplast
    ensures
        x <= xp0 ==> result == fp0,
        x >= xplast ==> result == fplast
{
    if x <= xp0 {
        proof {
            if x >= xplast {
                if xp0 < xplast {
                    assert(x < xplast);
                    assert(!(x >= xplast));
                } else {
                    assert(fp0 == fplast);
                }
            }
        }
        fp0
    } else if x >= xplast {
        fplast
    } else {
        fp0
    }
}
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): establish helper precondition as loop invariant; build result by mapping x to boundary values */
    let mut res: Vec<i32> = Vec::new();
    assert(xp.len() > 0);
    assert(fp.len() == xp.len());
    let xp0 = xp[0];
    let xplast = xp[xp.len() - 1];
    let fp0 = fp[0];
    let fplast = fp[fp.len() - 1];

    if xp.len() >= 2 {
        proof {
            let j: int = (xp.len() as int) - 1;
            assert(0 <= 0);
            assert(0 < j);
            assert(j < xp.len() as int);
            assert(forall|i: int, jj: int| 0 <= i < jj < xp.len() as int ==> xp[i] < xp[jj]));
            assert(xp[0] < xp[xp.len() - 1]);
        }
        proof { assert(xp0 == xp[0]); assert(xplast == xp[xp.len() - 1]); }
        assert(xp0 < xplast);

        let mut i: usize = 0;
        while i < x.len()
            invariant
                (i as int) <= x.len(),
                res.len() == (i as int),
                xp.len() > 0,
                fp.len() == xp.len(),
                xp0 < xplast || fp0 == fplast,
                forall|k: int| 0 <= k < (i as int) ==> (
                    (x[k] <= xp0 ==> res[k] == fp0) &&
                    (x[k] >= xplast ==> res[k] == fplast)
                )
            decreases (x.len() as int) - (i as int)
        {
            assert(xp0 < xplast || fp0 == fplast);
            let xi = x[i];
            let val = select_value(xi, xp0, xplast, fp0, fplast);
            res.push(val);
            proof {
                assert(xi <= xp0 ==> val == fp0);
                assert(xi >= xplast ==> val == fplast);
            }
            i += 1;
        }
    } else {
        proof { assert(fp0 == fplast); }
        let mut i: usize = 0;
        while i < x.len()
            invariant
                (i as int) <= x.len(),
                res.len() == (i as int),
                xp.len() > 0,
                fp.len() == xp.len(),
                xp0 < xplast || fp0 == fplast,
                forall|k: int| 0 <= k < (i as int) ==> (
                    (x[k] <= xp0 ==> res[k] == fp0) &&
                    (x[k] >= xplast ==> res[k] == fplast)
                )
            decreases (x.len() as int) - (i as int)
        {
            assert(xp0 < xplast || fp0 == fplast);
            let xi = x[i];
            let val = select_value(xi, xp0, xplast, fp0, fplast);
            res.push(val);
            proof {
                assert(xi <= xp0 ==> val == fp0);
                assert(xi >= xplast ==> val == fplast);
            }
            i += 1;
        }
    }

    assert(res.len() == x.len());
    assert(xp0 == xp[0]);
    assert(xplast == xp[xp.len() - 1]);
    assert(fp0 == fp[0]);
    assert(fplast == fp[fp.len() - 1]);
    assert(forall|k: int| 0 <= k < res.len() ==> (
        (x[k] <= xp[0] ==> res[k] == fp[0]) &&
        (x[k] >= xp[xp.len() - 1] ==> res[k] == fp[fp.len() - 1])
    ));

    res
}
// </vc-code>

}
fn main() {}