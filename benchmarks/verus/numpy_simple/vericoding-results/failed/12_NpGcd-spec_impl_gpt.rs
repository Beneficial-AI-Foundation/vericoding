// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arithmetic helpers for abs/max/min over mathematical ints */
pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

/* helper modified by LLM (iteration 5): max over mathematical ints */
pub open spec fn max_int(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

/* helper modified by LLM (iteration 5): min over mathematical ints */
pub open spec fn min_int(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

// </vc-helpers>

// <vc-spec>
fn gcd_int(a: i8, b: i8) -> (result: i8)
    ensures
        result >= 0,
        (a as int) % (result as int) == 0,
        (b as int) % (result as int) == 0,
        forall|d: int| d > 0 && #[trigger] ((a as int) % d) == 0 && #[trigger] ((b as int) % d) == 0 ==> d <= (result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): search for a common divisor with safe int loop and invariants; ensure nonzero, non-overflowing result */
    let ai: int = a as int;
    let bi: int = b as int;

    let x: int = if ai >= 0 { ai } else { -ai };
    let y: int = if bi >= 0 { bi } else { -bi };
    let n_exec: int = if x >= y { x } else { y };

    let mut i: int = 1;
    let mut best: int = 0;

    while i <= n_exec
        invariant
            1 <= i,
            i <= n_exec + 1,
            0 <= best,
            best <= i - 1,
            best == 0 || (ai % best == 0 && bi % best == 0),
            forall|d: int| 1 <= d && d <= i - 1 && ai % d == 0 && bi % d == 0 ==> d <= best,
        decreases n_exec + 1 - i
    {
        if ai % i == 0 && bi % i == 0 {
            best = i;
        }
        i = i + 1;
    }

    if best == 0 {
        // n_exec == 0; choose 1 since it divides all integers
        best = 1;
        proof {
            assert(ai % 1 == 0);
            assert(bi % 1 == 0);
        }
    }

    let out_int: int = if best <= 127 { best } else { 1 };
    let result: i8 = out_int as i8;

    proof {
        if out_int == best {
            assert(ai % (result as int) == 0);
            assert(bi % (result as int) == 0);
        } else {
            assert(out_int == 1);
            assert(ai % 1 == 0);
            assert(bi % 1 == 0);
        }
    }

    result
}
// </vc-code>


}
fn main() {}