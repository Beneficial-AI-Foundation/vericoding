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
/* helper modified by LLM (iteration 5): use i8 for computation to avoid ghost type in executable code */
fn compute_power(base: i8, exp: u8) -> (result: i8)
    ensures result == int_pow(base as int, exp as nat) as i8,
{
    let mut res: i8 = 1;
    let mut i: u8 = 0;
    while i < exp
        invariant
            0 <= i && i <= exp,
            res == int_pow(base as int, i as nat) as i8,
        decreases exp - i
    {
        res = res * base;
        i += 1;
    }
    res
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
/* code modified by LLM (iteration 5): no changes needed, helper function fixed */
{
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;

    while i < n
        invariant
            0 <= i && i <= n,
            n == a.len() && n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == int_pow(a@[j] as int, b@[j] as nat),
        decreases n - i
    {
        result.push(compute_power(a[i], b[i]));
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}