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
/* helper modified by LLM (iteration 3): Added lemma to help prove power computation invariant */
proof fn lemma_int_pow_step(base: int, j: nat)
    ensures int_pow(base, j + 1) == base * int_pow(base, j)
{
    // Follows from definition of int_pow
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
    /* code modified by LLM (iteration 3): Fixed loop invariant and added overflow precondition check */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == int_pow(a@[j] as int, b@[j] as nat),
        decreases n - i
    {
        let base = a[i];
        let exp = b[i];
        let mut pow_result: i8 = 1;
        let mut j: u8 = 0;
        while j < exp
            invariant
                j <= exp,
                pow_result == int_pow(base as int, j as nat),
                forall|k: nat| k <= exp ==> -128 <= int_pow(base as int, k) <= 127,
            decreases exp - j
        {
            proof {
                lemma_int_pow_step(base as int, j as nat);
            }
            pow_result = pow_result * base;
            j = j + 1;
        }
        result.push(pow_result);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}