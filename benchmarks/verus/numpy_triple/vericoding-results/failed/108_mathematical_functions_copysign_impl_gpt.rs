// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec abs for i8 */
pub open spec fn abs_i8(x: i8) -> int {
    if x >= 0 { x as int } else { -(x as int) }
}

/* helper modified by LLM (iteration 4): spec copysign on ints */
pub open spec fn copysign_int(x: i8, s: i8) -> int {
    let m = abs_i8(x);
    if s >= 0 { m } else { -m }
}

/* helper modified by LLM (iteration 4): lemma showing bounds for abs_i8 */
pub proof fn lemma_abs_bounds(x: i8)
    ensures
        0 <= abs_i8(x),
        abs_i8(x) <= 128,
{
    if x >= 0 {
        assert(abs_i8(x) == x as int);
        assert(0 <= x as int);
        assert(x as int <= 127);
        assert(x as int <= 128);
    } else {
        let xi: int = x as int;
        assert(xi <= -1);
        assert(abs_i8(x) == -xi);
        if x == -128i8 {
            assert(abs_i8(x) == 128);
        } else {
            assert(-127 <= xi && xi <= -1);
            assert(-xi <= 127);
        }
        assert(abs_i8(x) <= 128);
    }
}

// </vc-helpers>

// <vc-spec>
fn copysign(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Basic behavior: sign copying with magnitude preservation */
            (x2@[i] >= 0 ==> result@[i] as int == if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            (x2@[i] < 0 ==> result@[i] as int == if x1@[i] >= 0 { -(x1@[i] as int) } else { x1@[i] as int }) &&
            /* Magnitude preservation property: |result[i]| = |x1[i]| */
            (if result@[i] >= 0 { result@[i] as int } else { -(result@[i] as int) }) == 
            (if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            /* Sign copying property: result has same sign as x2 */
            (x2@[i] >= 0 ==> result@[i] >= 0) &&
            (x2@[i] < 0 ==> result@[i] < 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): strengthen loop invariants and prove index preconditions; compute elementwise sign copy using wider ints */
    let n: usize = x1.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x1.len(),
            n == x2.len(),
            0 <= i,
            i <= n,
            result.len() == i,
        decreases n - i
    {
        proof { assert(i < n); assert(n == x1.len()); assert(n == x2.len()); }
        let a: i8 = x1[i];
        let b: i8 = x2[i];
        let ai16: i16 = a as i16;
        let m16: i16 = if ai16 >= 0 { ai16 } else { -ai16 };
        let ri16: i16 = if b >= 0 { m16 } else { -m16 };
        let r: i8 = if ri16 <= 127 { ri16 as i8 } else { -128i8 };
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}