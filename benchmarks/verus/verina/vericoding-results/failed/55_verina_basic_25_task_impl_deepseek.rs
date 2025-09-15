// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type conversion from u32 to nat */
fn sum(n: nat) -> (s: nat)
    ensures s == (n * (n + 1)) / 2,
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev = sum((n - 1) as nat);
        prev + n
    }
}

proof fn sum_formula_lemma(n: nat)
    ensures (n * (n + 1)) % 2 == 0,
    decreases n
{
    if n > 0 {
        sum_formula_lemma((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use proper nat type conversion and ghost variable */
{
    ghost {
        sum_formula_lemma(n as nat);
    }
    
    if n == 0 {
        (0, 0.0)
    } else {
        let total: u32 = ((n as u64) * (n as u64 + 1) / 2) as u32;
        let average = (total as f64) / (n as f64);
        (total, average)
    }
}
// </vc-code>

}
fn main() {}