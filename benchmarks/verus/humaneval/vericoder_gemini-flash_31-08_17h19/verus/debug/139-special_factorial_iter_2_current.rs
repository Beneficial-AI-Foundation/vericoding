use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}
// pure-end
// pure-end

spec fn brazilian_factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}
// pure-end

// <vc-helpers>
#[verifier(external_body)]
#[cfg(target_arch = "x86_64")]
pub fn mul_checks_overflow(a: u64, b: u64) -> (res: (u64, bool))
    ensures
        res.0 as nat == a as nat * b as nat,
        res.1 == (a as nat * b as nat > u64::MAX),
{
    let (res, overflows) = a.overflowing_mul(b);
    (res, overflows)
}

#[verifier(external_body)]
#[cfg(target_arch = "aarch64")]
pub fn mul_checks_overflow(a: u64, b: u64) -> (res: (u64, bool))
    ensures
        res.0 as nat == a as nat * b as nat,
        res.1 == (a as nat * b as nat > u64::MAX),
{
    let (res, overflows) = a.overflowing_mul(b);
    (res, overflows)
}

// Helper function to calculate factorial and check for overflow
spec fn factorial_u64_upper_bound(n: nat) -> (res: nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial_u64_upper_bound((n - 1) as nat)
    }
}

proof fn lemma_factorial_u64_upper_bound_is_factorial(n: nat)
    ensures factorial_u64_upper_bound(n) == factorial(n)
    decreases n
{
    if n <= 1 {
        assert(factorial_u64_upper_bound(n) == 1);
        assert(factorial(n) == 1);
    } else {
        lemma_factorial_u64_upper_bound_is_factorial((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    // post-conditions-start
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n_nat: nat = n as nat;
    let mut current_n: u64 = n;
    let mut result_factorial: u64 = 1;

    if n_nat > u64::MAX {
        return None;
    }

    let mut i: u64 = 2; // Start from 2 because 1! = 1, and 0! = 1
    let mut overflowed_fact: bool = false;

    while i <= n
        invariant
            i as nat <= n_nat + 1,
            // (factorial(i-1) <= u64::MAX && !overflowed_fact) ==> result_factorial == factorial(i-1),
            // (factorial(i-1) > u64::MAX) ==> overflowed_fact,
            (overflowed_fact == true) == (factorial(i as nat - 1) > u64::MAX),
            // If overflowed_fact is true, it means the intermediate factorial calculation has exceeded u64::MAX
            // and `result_factorial` holds the truncated result.
            // If we have not overflowed, `result_factorial` should store `factorial(i-1)`.
            (overflowed_fact == false) ==> (result_factorial == factorial(i as nat - 1)),
            (overflowed_fact == true) ==> (result_factorial as nat == factorial(i as nat - 1)), // In case of overflow, result_factorial stores the modulo result
            // (result_factorial as nat == factorial(i as nat - 1)) || (factorial(i as nat - 1) > u64::MAX),
    {
        let (new_res, overflows) = mul_checks_overflow(result_factorial, i);
        result_factorial = new_res;
        overflowed_fact = overflowed_fact || overflows;
        i = i + 1;
    }

    proof {
        lemma_factorial_u64_upper_bound_is_factorial(n_nat); // Ensure factorial_u64_upper_bound == factorial
    }

    if overflowed_fact {
        assert(factorial(n_nat) > u64::MAX); // If overflowed_fact is true, then n! > u64::MAX
        return None;
    }

    // Now, `result_factorial` holds `factorial(n)` if it didn't overflow
    // and `!overflowed_fact` is true.

    let mut accumulator: u64 = 1;
    let mut overflowed_bf: bool = false;
    let mut k: u64 = 1;

    while k <= n
        invariant
            k as nat <= n_nat + 1,
            // The loop calculates product of factorial(1), factorial(2), ..., factorial(k-1).
            // This corresponds to brazilian_factorial(k-1).
            (overflowed_bf == true) == (brazilian_factorial(k as nat - 1) > u64::MAX),
            (overflowed_bf == false) ==> (accumulator == brazilian_factorial(k as nat - 1)),
            (overflowed_bf == true) ==> (accumulator as nat == brazilian_factorial(k as nat - 1)), // In case of overflow, accumulator stores the modulo result

            // We need to prove that factorial(k) does not overflow inside the loop,
            // or handle the overflow correctly.
            // This is effectively handled by `current_factorial_k` below.

            // The invariant must connect `accumulator` to `brazilian_factorial(k-1)`.
            // The values for `factorial_k` are dynamically calculated, so we need to ensure the values are correct.
    {
        // Calculate factorial(k) for this iteration
        let mut factorial_k: u64 = 1;
        let mut overflowed_f_k: bool = false;
        let mut j: u64 = 2;

        while j <= k
            invariant
                j as nat <= k as nat + 1,
                (overflowed_f_k == true) == (factorial(j as nat - 1) > u64::MAX),
                (overflowed_f_k == false) ==> (factorial_k == factorial(j as nat - 1)),
                (overflowed_f_k == true) ==> (factorial_k as nat == factorial(j as nat - 1)), // result of modulo op in case of overflow
        {
            let (new_res, overflows) = mul_checks_overflow(factorial_k, j);
            factorial_k = new_res;
            overflowed_f_k = overflowed_f_k || overflows;
            j = j + 1;
        }

        if overflowed_f_k {
            // Factorial(k) overflowed. This means current_brazilian_factorial will also overflow.
            overflowed_bf = true;
            // No need to calculate further; subsequent products will also overflow.
            // We can break, but for simpler proof, just continue with overflowed_bf true.
        } else if !overflowed_bf {
            // Only perform multiplication if accumulator hasn't overflowed yet
            let (new_acc, overflows) = mul_checks_overflow(accumulator, factorial_k);
            accumulator = new_acc;
            overflowed_bf = overflowed_bf || overflows;
        }
        k = k + 1;
    }

    if overflowed_bf {
        assert(brazilian_factorial(n_nat) > u64::MAX);
        None
    } else {
        assert(accumulator == brazilian_factorial(n_nat));
        Some(accumulator)
    }
}
// </vc-code>

} // verus!
fn main() {}