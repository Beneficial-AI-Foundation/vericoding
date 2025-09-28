// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): returns a + k * b as a simple arithmetic identity */
proof fn mul_nonneg_preserves_order(a: int, b: int, k: int) -> (res: int)
    requires
        k >= 0,
    ensures
        res == a + k * b,
{
    a + k * b
}

/* helper modified by LLM (iteration 3): monotonicity of arithmetic progression based on step sign */
proof fn lower_bound_for_progression(start: int, step: int, i: int)
    requires
        i >= 0,
    ensures
        if step > 0 { start <= start + i * step } else if step < 0 { start + i * step <= start } else { start + i * step == start },
{
}

/* helper modified by LLM (iteration 3): derive i8 range from explicit integer bounds */
proof fn bounds_imply_i8_range(x: int, lo: int, hi: int)
    requires
        lo == -128,
        hi == 127,
        lo <= x,
        x <= hi,
    ensures
        -128 <= x && x <= 127,
{
}
// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): avoid using 'int' in exec code; compute via i32 then cast to i8 */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
        decreases n - i
    {
        let vi32: i32 = (start as i32) + (i as i32) * (step as i32);
        let val: i8 = vi32 as i8;
        v.push(val);
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}