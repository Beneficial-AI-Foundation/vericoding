// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_int(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove abs_int is nonnegative */
proof fn lemma_abs_int_nonneg(x: int)
    ensures
        abs_int(x) >= 0,
{
    if x < 0 {
        assert(-x >= 0);
    } else {
        assert(x >= 0);
    }
}

/* helper modified by LLM (iteration 5): characterization of abs_int by sign */
proof fn lemma_abs_int_char(x: int)
    ensures
        x >= 0 ==> abs_int(x) == x,
        x < 0 ==> abs_int(x) == -x,
{
    if x < 0 {
        assert(abs_int(x) == -x);
    } else {
        assert(abs_int(x) == x);
    }
}
// </vc-helpers>

// <vc-spec>
fn abs(a: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == abs_int(a[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid exec `int` usage; compute i8 abs with MIN guard; maintain nonnegativity and length invariants */
    let n = a.len();
    let mut res: Vec<i8> = Vec::new();
    while res.len() < n
        invariant
            n == a.len(),
            res.len() <= n,
            forall|j: int| 0 <= j < res.len() ==> res@[j] >= 0,
        decreases n - res.len()
    {
        let idx = res.len();
        let v: i8 = a[idx];
        let y: i8 = if v < 0 {
            if v == i8::MIN { 0 } else { -v }
        } else {
            v
        };
        res.push(y);
    }
    res
}
// </vc-code>


}
fn main() {}