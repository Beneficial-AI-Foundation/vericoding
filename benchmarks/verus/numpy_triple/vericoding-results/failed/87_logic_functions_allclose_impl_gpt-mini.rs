// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate int_abs of i8 differences to definition */
proof fn abs_diff_i8_eq(ai: i8, bi: i8)
    ensures
        int_abs((ai - bi) as int) == (if (ai as int - bi as int) >= 0 { ai as int - bi as int } else { -(ai as int - bi as int) }),
{
    if ai as int - bi as int >= 0 {
        assert(int_abs((ai - bi) as int) == ai as int - bi as int);
    } else {
        assert(int_abs((ai - bi) as int) == -(ai as int - bi as int));
    }
}

/* helper modified by LLM (iteration 5): relate int_abs of i8 value to its int form */
proof fn abs_i8_eq(x: i8)
    ensures
        int_abs(x as int) == (if x as int >= 0 { x as int } else { -(x as int) }),
{
    if x as int >= 0 {
        assert(int_abs(x as int) == x as int);
    } else {
        assert(int_abs(x as int) == -(x as int));
    }
}

// </vc-helpers>

// <vc-spec>
fn allclose(a: Vec<i8>, b: Vec<i8>, rtol: i8, atol: i8) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures 
        result == (forall|i: int| 0 <= i < a@.len() ==> 
            int_abs((a[i] - b[i]) as int) <= (atol as int + rtol as int * int_abs(b[i] as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using usize, compute int values and maintain invariant */
    let n: usize = a.len();
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < n
        invariant
            i <= n,
            ok == forall|j: int| 0 <= j < (i as int) ==> int_abs((a@[j] - b@[j]) as int) <= (atol as int + rtol as int * int_abs(b@[j] as int))),
        decreases n - i
    {
        let ai: i8 = a[i];
        let bi: i8 = b[i];
        let ai_int: int = ai as int;
        let bi_int: int = bi as int;
        let diff: int = ai_int - bi_int;
        let absdiff: int = if diff >= 0 { diff } else { -diff };
        let rhs: int = (atol as int) + (rtol as int) * int_abs(bi_int);
        let cond_rt: bool = absdiff <= rhs;
        proof {
            abs_diff_i8_eq(ai, bi);
            abs_i8_eq(bi);
            assert(int_abs((ai - bi) as int) == absdiff);
            assert((atol as int + rtol as int * int_abs(bi as int)) == rhs);
            assert(cond_rt == (int_abs((ai - bi) as int) <= (atol as int + rtol as int * int_abs(bi as int))));
        }
        ok = ok && cond_rt;
        i = i + 1;
    }
    ok
}

// </vc-code>

}
fn main() {}