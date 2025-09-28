// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value for int */
fn abs_int(a: int) -> (r: int)
    ensures
        r >= 0,
        r == if a >= 0 { a } else { -a },
{
    if a >= 0 {
        r = a;
    } else {
        r = -a;
    }
}

/* helper modified by LLM (iteration 5): recursive gcd on nonnegative ints using Euclid's algorithm */
fn gcd_impl(a: int, b: int) -> (r: int)
    requires
        a >= 0,
        b >= 0,
    decreases
        b,
    ensures
        r >= 0,
        a % r == 0,
        b % r == 0,
        forall|d: int| d > 0 && a % d == 0 && b % d == 0 ==> d <= r,
{
    if b == 0 {
        r = a;
    } else {
        let rem = a % b;
        proof {
            assert(0 <= rem && rem < b);
        }
        let sub = gcd_impl(b, rem);
        r = sub;
    }
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
    /* code modified by LLM (iteration 5): compute gcd by taking absolute values and calling gcd_impl with proofs */
    let ai: int = a as int;
    let bi: int = b as int;
    let aa = abs_int(ai);
    let bb = abs_int(bi);
    let g = gcd_impl(aa, bb);
    proof {
        // prove divisibility for original signed inputs using the fact that aa and bb are absolute values
        if ai >= 0 {
            assert(aa == ai);
            assert(ai % g == 0);
        } else {
            assert(aa == -ai);
            assert(aa % g == 0);
            // from aa == -ai and aa % g == 0 conclude ai % g == 0
            assert(ai % g == 0);
        }
        if bi >= 0 {
            assert(bb == bi);
            assert(bi % g == 0);
        } else {
            assert(bb == -bi);
            assert(bb % g == 0);
            assert(bi % g == 0);
        }
        assert(g >= 0);
    }
    g as i8
}

// </vc-code>


}
fn main() {}