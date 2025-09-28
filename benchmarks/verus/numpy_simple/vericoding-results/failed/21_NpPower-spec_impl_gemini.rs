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
fn compute_power(base: i8, exp: u8) -> (result: i8)
    requires
        i8::MIN <= int_pow(base as int, exp as nat),
        int_pow(base as int, exp as nat) <= i8::MAX,
    ensures
        result as int == int_pow(base as int, exp as nat),
{
    let mut res: i64 = 1;
    let mut i: u8 = 0;
    while i < exp
        invariant
            i <= exp,
            res == int_pow(base as int, i as nat),
        decreases exp - i
    {
        res = res * (base as i64);
        i = i + 1;
    }
    res as i8
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == int_pow(a@[j] as int, b@[j] as nat),
        decreases a.len() - i
    {
        let base = a[i];
        let exp = b[i];
        
        let val = compute_power(base, exp);
        
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}