// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove cast distributes over subtraction */
proof fn cast_sub_i32(a: i32, b: i32) ensures (a - b) as int == a as int - b as int {
    proof {
        let A: int = a as int;
        let B: int = b as int;
        assert(A - B == (a - b) as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn allclose(a: Vec<i32>, b: Vec<i32>, rtol: i32, atol: i32) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures 
        result == (forall|i: int| 0 <= i < a.len() ==> 
            int_abs((a[i] - b[i]) as int) <= (atol + rtol * int_abs(b[i] as int)) as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): loop with invariant relating ok to forall and stepwise proof */
    let mut i: nat = 0;
    let len: nat = a.len();
    let mut ok: bool = true;
    while i < len
        invariant i <= len;
        invariant ok == (forall|j: int| 0 <= j && j < i as int ==> int_abs((a[j as nat] - b[j as nat]) as int) <= (atol as int + rtol as int * int_abs(b[j as nat] as int)));
        decreases len - i;
    {
        let ai: i32 = a[i];
        let bi: i32 = b[i];
        let cond: bool = int_abs((ai - bi) as int) <= (atol as int + rtol as int * int_abs(bi as int));
        let prev_ok: bool = ok;
        ok = prev_ok && cond;
        proof {
            assert(prev_ok == (forall|j: int| 0 <= j && j < i as int ==> int_abs((a[j as nat] - b[j as nat]) as int) <= (atol as int + rtol as int * int_abs(b[j as nat] as int))));
            assert(cond == (int_abs((a[i as nat] - b[i as nat]) as int) <= (atol as int + rtol as int * int_abs(b[i as nat] as int))));
            assert(ok == (forall|j: int| 0 <= j && j < (i as int) + 1 ==> int_abs((a[j as nat] - b[j as nat]) as int) <= (atol as int + rtol as int * int_abs(b[j as nat] as int))));
        }
        i = i + 1;
    }
    result = ok;
}
// </vc-code>

}
fn main() {}