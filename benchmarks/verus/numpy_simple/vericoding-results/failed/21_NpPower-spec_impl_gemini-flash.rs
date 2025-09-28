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

// </vc-helpers>

// <vc-spec>
fn power(a: Vec<i8>, b: Vec<u8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == int_pow(a@[i] as int, b@[i] as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed type conversion from `int` and `nat` to `i8` by introducing `as i8`. Moved loop invariants outside `while` statements directly in the body of `power()` function for brevity and compliance with new requirements.] */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: nat = 0;

    while i < a.len()
        invariant // loop invariants:
            result.len() == i,
            0 <= i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == int_pow(a@[j] as int, b@[j] as nat),
        decreases a.len() - i
    {

        let base: i8 = a[i as usize];
        let exp: u8 = b[i as usize];

        let mut current_result: i8 = 1;
        let mut current_exp: u8 = exp;

        while current_exp > 0
            invariant // loop invariants:
                current_exp <= exp,
                current_exp >= 0,
                // Note: The loop calculates base^exp. `current_result` is `base^(exp - current_exp)`
                // So, after `current_exp` iterations, `current_result` becomes `base^(exp - 0) = base^exp`.
                int_pow(base as int, (exp - current_exp) as nat) == current_result as int,
            decreases current_exp
        {
            current_result = (current_result as int * base as int) as i8;
            current_exp = current_exp - 1;
        }

        result.push(current_result);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}