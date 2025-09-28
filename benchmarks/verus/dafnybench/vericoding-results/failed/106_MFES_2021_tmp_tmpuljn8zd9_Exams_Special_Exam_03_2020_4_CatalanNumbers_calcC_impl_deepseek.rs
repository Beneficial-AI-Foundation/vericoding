use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else {
        n * factorial((n - 1) as nat)
    }
}

spec fn binomial_coeff(n: nat, k: nat) -> nat
    decreases n, k
{
    if k == 0 || k == n {
        1nat
    } else if n == 0 || k > n {
        0nat
    } else {
        binomial_coeff((n - 1) as nat, (k - 1) as nat) + binomial_coeff((n - 1) as nat, k)
    }
}

proof fn C_is_catalan(n: nat) 
    ensures C(n) == binomial_coeff(2*n, n) / ((n as int) + 1) as nat
    decreases n
{
    if n == 0 {
        assert(C(0) == 1);
        assert(binomial_coeff(0, 0) == 1);
    } else {
        C_is_catalan((n - 1) as nat);
        let prev = C((n - 1) as nat);
        assert(prev == binomial_coeff(2*(n-1) as nat, (n-1) as nat) / (n as int) as nat);
        
        proof {
            let two_n_minus_one = (2*n as int - 1) as nat;
            let double_prev = binomial_coeff(two_n_minus_one, (n-1) as nat) + binomial_coeff(two_n_minus_one, n);
            assert(double_prev == binomial_coeff(2*n, n));
        }
    }
}

proof fn factorial_properties(n: nat, k: nat)
    requires k <= n
    ensures factorial(n) / factorial(k) >= factorial((n - k) as nat)
    decreases n
{
    if n > 0 && k > 0 {
        factorial_properties((n - 1) as nat, (k - 1) as nat);
    }
}

proof fn binomial_properties(n: nat, k: nat)
    requires k <= n
    ensures binomial_coeff(n, k) == factorial(n) / (factorial(k) * factorial((n - k) as nat))
    decreases n
{
    if n > 0 && k > 0 && k < n {
        binomial_properties((n - 1) as nat, (k - 1) as nat);
        binomial_properties((n - 1) as nat, k);
        factorial_properties(n, k);
    } else if k == 0 {
        assert(factorial(n) / (factorial(0) * factorial(n)) == 1);
    } else if k == n {
        assert(factorial(n) / (factorial(n) * factorial(0)) == 1);
    }
}

proof fn catalan_recurrence(n: nat)
    requires n > 0
    ensures C(n) == ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
{
    // This is the definition of C(n) for n > 0
    // No proof needed since it's defined this way
}

proof fn verify_step(i: nat)
    requires i > 0
    ensures C(i) == ((4 * (i as int) - 2) * (C((i - 1) as nat) as int) / ((i as int) + 1)) as nat
{
    // This follows directly from the definition
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof { C_is_catalan(0); }
        return 1;
    }
    
    let mut res: u64 = 1;
    let mut i: u64 = 1;
    
    while i <= n
        invariant
            i <= n + 1,
            res == C((i - 1) as nat),
        decreases (n - i) as int
    {
        let prev_i = i;
        assert(prev_i >= 1) by {
            assert(i >= 1);
        }
        assert(prev_i <= n);
        
        proof {
            verify_step(prev_i as nat);
        }
        
        let temp1: u64 = (4 * i).checked_sub(2).unwrap();
        let temp2: u64 = temp1.checked_mul(res).unwrap();
        let next_res: u64 = temp2.checked_div(i + 1).unwrap();
        
        i = i + 1;
        res = next_res;
        
        proof {
            assert(res == C((i - 1) as nat)) by {
                assert(C(prev_i as nat) == ((4 * (prev_i as int) - 2) * (C((prev_i - 1) as nat) as int) / ((prev_i as int) + 1)) as nat);
                assert(next_res == C(prev_i as nat));
                assert(i == prev_i + 1);
            }
        }
    }
    
    res
}
// </vc-code>

fn main() {}

}