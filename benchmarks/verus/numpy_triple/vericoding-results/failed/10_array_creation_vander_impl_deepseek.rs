// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_pow_int_monotonic(base: int, exp1: nat, exp2: nat)
    requires
        base >= 0,
        exp1 <= exp2,
    ensures
        pow_int(base, exp1) <= pow_int(base, exp2),
{
    if exp1 == exp2 {
    } else {
        lemma_pow_int_monotonic(base, exp1, (exp2 - 1) as nat);
    }
}

proof fn lemma_pow_int_positive(base: int, exp: nat)
    requires
        base >= 0,
    ensures
        pow_int(base, exp) >= 0,
{
    if exp == 0 {
    } else {
        lemma_pow_int_positive(base, (exp - 1) as nat);
    }
}

/* helper modified by LLM (iteration 5): fix type conversion for x@[i] from usize to int */
spec fn compute_power_spec(base: i8, exp: nat) -> (result: i8)
    requires
        base >= 0,
        pow_int(base as int, exp) <= 0x7f,
    ensures
        result as int == pow_int(base as int, exp),
{
    if exp == 0 {
        1
    } else {
        let sub_result = compute_power_spec(base, (exp - 1) as nat);
        (base as int * sub_result as int) as i8
    }
}

fn compute_power(base: i8, exp: usize) -> (result: i8)
    requires
        base >= 0,
        pow_int(base as int, exp as nat) <= 0x7f,
    ensures
        result as int == pow_int(base as int, exp as nat),
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let sub_exp = exp - 1;
        let sub_result = compute_power(base, sub_exp);
        (base as i32 * sub_result as i32) as i8
    }
}

// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type conversion errors in x@[i] access */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let n = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == m,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m ==> result@[k]@[j] as int == pow_int(x@[k] as int, (m - 1 - j) as nat),
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                row@.len() == j,
                forall|l: int| 0 <= l < j ==> row@[l] as int == pow_int((x@[i as int] as int), (m - 1 - l) as nat),
        {
            let exp_val = m - 1 - j;
            let xi = x[i];
            proof {
                lemma_pow_int_positive(xi as int, exp_val as nat);
            }
            let power_val = compute_power(xi, exp_val);
            row.push(power_val);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}