// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(w: int, h: int, k: int) -> bool {
    w >= 3 && h >= 3 && w <= 100 && h <= 100 && 
    k >= 1 && k <= ((if w <= h { w } else { h }) + 1) / 4 &&
    w - 4 * k >= 3 && h - 4 * k >= 3
}

spec fn perimeter(w: int, h: int) -> int {
    w * 2 + (h - 2) * 2
}

spec fn compute_sum(w: int, h: int, k: int) -> int
    decreases k when k > 0
{
    if k <= 0 { 0 }
    else { 
        perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec lemma expressing compute_sum unfolding for k>0 */
spec fn compute_sum_unfold(w: int, h: int, k: int) -> bool {
    if k <= 0 { true } else { compute_sum(w, h, k) == perimeter(w, h) + compute_sum(w - 4, h - 4, k - 1) }
}
// </vc-helpers>

// <vc-spec>
fn gild_cells(w: i8, h: i8, k: i8) -> (result: i8)
    requires valid_input(w as int, h as int, k as int)
    ensures result as int == compute_sum(w as int, h as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterative accumulation with inline proof using compute_sum definition */
    let mut acc: i8 = 0;
    let mut cw: i8 = w;
    let mut ch: i8 = h;
    let mut ck: i8 = k;

    while ck > 0
        invariant
            acc as int + compute_sum(cw as int, ch as int, ck as int) == compute_sum(w as int, h as int, k as int),
            ck as int >= 0,
            cw as int >= 3,
            ch as int >= 3,
        decreases ck
    {
        proof {
            // ck > 0, so compute_sum unfolds to perimeter + recursive call
            assert(ck as int > 0);
            assert(compute_sum(cw as int, ch as int, ck as int) ==
                   perimeter(cw as int, ch as int) + compute_sum(cw as int - 4, ch as int - 4, ck as int - 1));
        }
        let p: i8 = cw * 2 + (ch - 2) * 2;
        acc = acc + p;
        cw = cw - 4;
        ch = ch - 4;
        ck = ck - 1;
    }

    proof {
        assert(ck as int <= 0);
        assert(compute_sum(cw as int, ch as int, ck as int) == 0);
        assert(acc as int + compute_sum(cw as int, ch as int, ck as int) == compute_sum(w as int, h as int, k as int));
    }

    acc
}
// </vc-code>


}

fn main() {}