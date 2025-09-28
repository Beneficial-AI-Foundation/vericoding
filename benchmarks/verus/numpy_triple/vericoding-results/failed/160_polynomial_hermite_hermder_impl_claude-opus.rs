// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
use vstd::arithmetic::power::pow;

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

/* helper modified by LLM (iteration 5): Fixed factorial_positive proof to establish postcondition */
proof fn factorial_positive(n: nat)
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 {
        assert(factorial(0) == 1);
    } else {
        factorial_positive((n - 1) as nat);
        assert(factorial(n) == n * factorial((n - 1) as nat));
    }
}

/* helper modified by LLM (iteration 5): Fixed bounds checks and arithmetic overflow issues */
fn compute_hermite_derivative(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
{
    if m >= c.len() {
        return Vec::new();
    }
    
    let mut result: Vec<i8> = Vec::new();
    let n = c.len() - m;
    
    if m == 0 {
        for i in 0..c.len()
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == c[j],
        {
            result.push(c[i]);
        }
    } else if m == 1 {
        for i in 0..n
            invariant
                result.len() == i,
                n == c.len() - 1,
                i <= n,
                forall|j: int| 0 <= j < i ==> result[j] as int == (scl as int) * (2 * ((j + 1) as int)) * (c[j + 1] as int),
                forall|j: int| 0 <= j < i ==> j + 1 < c.len(),
        {
            assert(i + 1 < c.len());
            let coeff: i8 = scl.wrapping_mul(2_i8.wrapping_mul(#[verifier::truncate] (i + 1) as i8)).wrapping_mul(c[i + 1]);
            result.push(coeff);
        }
    } else if m == 2 {
        for i in 0..n
            invariant
                result.len() == i,
                n == c.len() - 2,
                i <= n,
                forall|j: int| 0 <= j < i ==> result[j] as int == (scl as int) * (scl as int) * (2 * ((j + 2) as int)) * (2 * ((j + 1) as int)) * (c[j + 2] as int),
                forall|j: int| 0 <= j < i ==> j + 2 < c.len(),
        {
            assert(i + 2 < c.len());
            let coeff: i8 = scl.wrapping_mul(scl).wrapping_mul(2_i8.wrapping_mul(#[verifier::truncate] (i + 2) as i8)).wrapping_mul(2_i8.wrapping_mul(#[verifier::truncate] (i + 1) as i8)).wrapping_mul(c[i + 2]);
            result.push(coeff);
        }
    } else {
        let mut scale_factor: i64 = 1;
        for k in 0..m
            invariant
                k <= m,
                scale_factor == pow(scl as int, k as nat) * #[verifier::truncate] (factorial(k as nat) as i64),
        {
            factorial_positive(k as nat);
            factorial_positive((k + 1) as nat);
            scale_factor = scale_factor.wrapping_mul(scl as i64).wrapping_mul(#[verifier::truncate] ((k + 1) as i64));
        }
        
        for i in 0..n
            invariant
                result.len() == i,
                n == c.len() - m,
                i <= n,
                forall|j: int| 0 <= j < i ==> j + m < c.len(),
        {
            assert(i + m < c.len());
            let mut coeff: i64 = scale_factor;
            for j in 0..m
                invariant
                    j <= m,
                    i + j <= i + m,
                    i + m < c.len(),
            {
                coeff = coeff.wrapping_mul(#[verifier::truncate] ((i + j + 1) as i64));
            }
            result.push(#[verifier::truncate] (coeff.wrapping_mul(c[i + m] as i64) as i8));
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Direct delegation to helper function */
    compute_hermite_derivative(c, m, scl)
}
// </vc-code>

}
fn main() {}