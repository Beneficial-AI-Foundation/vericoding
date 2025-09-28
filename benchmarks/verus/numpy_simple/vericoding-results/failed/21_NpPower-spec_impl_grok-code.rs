// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * int_pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed function signature to name return value for ensures clause */
fn exec_int_pow(base: i8, exp: u8) -> (result: i8)
    ensures
        result as int == int_pow(base as int, exp as nat)
{
    let mut result = 1i8;
    let mut current_exp = exp;
    while current_exp > 0
    {
        result = result * base;
        current_exp -= 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn power(a: Vec<i8>, b: Vec<u8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == int_pow(a@[i] as int, b@[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, as verification is failing due to compilation error in helpers */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] as int == int_pow(a@[k], b@[k] as nat)
    {
        let pow_val = exec_int_pow(a[i], b[i]);
        result.push(pow_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}