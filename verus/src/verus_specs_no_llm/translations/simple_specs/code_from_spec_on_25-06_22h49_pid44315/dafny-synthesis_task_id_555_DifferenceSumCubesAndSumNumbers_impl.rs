use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for sum of numbers 1 to n
spec fn sum_numbers(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_numbers(n - 1) }
}

// Spec function for sum of cubes 1^3 to n^3
spec fn sum_cubes(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n * n * n + sum_cubes(n - 1) }
}

// Lemma to prove the formula for sum of numbers
proof fn lemma_sum_numbers_formula(n: nat)
    ensures sum_numbers(n) * 2 == n * (n + 1)
    decreases n
{
    if n == 0 {
        // Base case: sum_numbers(0) = 0, and 0 * 2 = 0 * 1 = 0
        assert(sum_numbers(0) == 0);
        assert(sum_numbers(0) * 2 == 0);
        assert(0 * (0 + 1) == 0);
    } else {
        // Inductive step
        lemma_sum_numbers_formula(n - 1);
        // We know: sum_numbers(n-1) * 2 == (n-1) * n
        assert(sum_numbers(n - 1) * 2 == (n - 1) * n);
        // We have: sum_numbers(n) == n + sum_numbers(n-1)
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        // So: sum_numbers(n) * 2 == (n + sum_numbers(n-1)) * 2
        assert(sum_numbers(n) * 2 == (n + sum_numbers(n - 1)) * 2);
        assert((n + sum_numbers(n - 1)) * 2 == n * 2 + sum_numbers(n - 1) * 2);
        assert(n * 2 + sum_numbers(n - 1) * 2 == n * 2 + (n - 1) * n);
        assert(n * 2 + (n - 1) * n == 2 * n + n * n - n);
        assert(2 * n + n * n - n == n + n * n);
        assert(n + n * n == n * (1 + n));
        assert(n * (1 + n) == n * (n + 1));
    }
}

// Lemma to prove the formula for sum of cubes
proof fn lemma_sum_cubes_formula(n: nat)
    ensures sum_cubes(n) * 4 == n * n * (n + 1) * (n + 1)
    decreases n
{
    if n == 0 {
        // Base case: sum_cubes(0) = 0, and 0 * 4 = 0
        assert(sum_cubes(0) == 0);
        assert(sum_cubes(0) * 4 == 0);
        assert(0 * 0 * (0 + 1) * (0 + 1) == 0);
    } else {
        // Inductive step
        lemma_sum_cubes_formula(n - 1);
        assert(sum_cubes(n - 1) * 4 == (n - 1) * (n - 1) * n * n);
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        
        // We need to show: sum_cubes(n) * 4 == n * n * (n + 1) * (n + 1)
        // sum_cubes(n) * 4 = (n^3 + sum_cubes(n-1)) * 4
        //                 = n^3 * 4 + sum_cubes(n-1) * 4
        //                 = n^3 * 4 + (n-1)^2 * n^2
        assert(sum_cubes(n) * 4 == (n * n * n + sum_cubes(n - 1)) * 4);
        assert((n * n * n + sum_cubes(n - 1)) * 4 == n * n * n * 4 + sum_cubes(n - 1) * 4);
        assert(n * n * n * 4 + sum_cubes(n - 1) * 4 == n * n * n * 4 + (n - 1) * (n - 1) * n * n);
        
        // Algebraic manipulation to show this equals n^2 * (n+1)^2
        let lhs = n * n * n * 4 + (n - 1) * (n - 1) * n * n;
        let rhs = n * n * (n + 1) * (n + 1);
        
        // Factor out n^2
        assert(lhs == n * n * (n * 4 + (n - 1) * (n - 1)));
        assert(rhs == n * n * (n + 1) * (n + 1));
        
        // Show n * 4 + (n-1)^2 == (n+1)^2
        assert(n * 4 + (n - 1) * (n - 1) == 4 * n + n * n - 2 * n + 1);
        assert(4 * n + n * n - 2 * n + 1 == n * n + 2 * n + 1);
        assert(n * n + 2 * n + 1 == (n + 1) * (n + 1));
    }
}

// Helper function to compute sum of numbers
fn compute_sum_numbers(n: u32) -> (result: u32)
    requires 
        n <= 65535, // Ensure no overflow in n * (n + 1)
        n % 2 == 0 || (n + 1) % 2 == 0 // Ensure n * (n + 1) is even
    ensures result as nat == sum_numbers(n as nat)
{
    proof {
        lemma_sum_numbers_formula(n as nat);
        // The lemma proves that sum_numbers(n) * 2 == n * (n + 1)
        // So sum_numbers(n) == n * (n + 1) / 2
        assert(sum_numbers(n as nat) * 2 == (n as nat) * ((n as nat) + 1));
        assert(sum_numbers(n as nat) == (n as nat) * ((n as nat) + 1) / 2);
        assert((n * (n + 1)) / 2 == (n as nat) * ((n as nat) + 1) / 2);
    }
    (n * (n + 1)) / 2
}

// Helper function to compute sum of cubes
fn compute_sum_cubes(n: u32) -> (result: u32)
    requires 
        n <= 255, // Ensure no overflow in n^2 * (n + 1)^2
        n * n <= u32::MAX / ((n + 1) * (n + 1)) // Additional overflow check
    ensures result as nat == sum_cubes(n as nat)
{
    proof {
        lemma_sum_cubes_formula(n as nat);
        // The lemma proves that sum_cubes(n) * 4 == n^2 * (n + 1)^2
        // So sum_cubes(n) == n^2 * (n + 1)^2 / 4
        assert(sum_cubes(n as nat) * 4 == (n as nat) * (n as nat) * ((n as nat) + 1) * ((n as nat) + 1));
        assert(sum_cubes(n as nat) == (n as nat) * (n as nat) * ((n as nat) + 1) * ((n as nat) + 1) / 4);
    }
    let n_plus_1 = n + 1;
    (n * n * n_plus_1 * n_plus_1) / 4
}

// Lemma to prove that sum of cubes is always >= sum of numbers for n >= 0
proof fn lemma_sum_cubes_ge_sum_numbers(n: nat)
    ensures sum_cubes(n) >= sum_numbers(n)
    decreases n
{
    if n == 0 {
        // Base case: both are 0
        assert(sum_cubes(0) == 0);
        assert(sum_numbers(0) == 0);
    } else if n == 1 {
        // sum_cubes(1) = 1, sum_numbers(1) = 1
        assert(sum_cubes(1) == 1 * 1 * 1 + sum_cubes(0));
        assert(sum_cubes(1) == 1 + 0);
        assert(sum_cubes(1) == 1);
        assert(sum_numbers(1) == 1 + sum_numbers(0));
        assert(sum_numbers(1) == 1 + 0);
        assert(sum_numbers(1) == 1);
    } else {
        // For n >= 2, we can show that n^3 >= n
        lemma_sum_cubes_ge_sum_numbers(n - 1);
        assert(sum_cubes(n - 1) >= sum_numbers(n - 1));
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        
        // Show n^3 >= n for n >= 2
        assert(n >= 2);
        assert(n * n >= n); // since n >= 2
        assert(n * n * n >= n * n); // multiply both sides by n
        assert(n * n >= n); // we know this
        assert(n * n * n >= n); // transitivity
        
        // Therefore sum_cubes(n) >= sum_numbers(n)
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        assert(sum_cubes(n) >= n + sum_cubes(n - 1)); // since n^3 >= n
        assert(sum_cubes(n) >= n + sum_numbers(n - 1)); // since sum_cubes(n-1) >= sum_numbers(n-1)
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        assert(sum_cubes(n) >= sum_numbers(n));
    }
}

fn DifferenceSumCubesAndSumNumbers(n: u32) -> (result: u32)
    requires 
        n <= 255,
        n % 2 == 0 || (n + 1) % 2 == 0,
        n * n <= u32::MAX / ((n + 1) * (n + 1))
    ensures
        result as nat == sum_cubes(n as nat) - sum_numbers(n as nat)
{
    proof {
        lemma_sum_cubes_formula(n as nat);
        lemma_sum_numbers_formula(n as nat);
        lemma_sum_cubes_ge_sum_numbers(n as nat);
    }
    
    let sum_cubes_val = compute_sum_cubes(n);
    let sum_numbers_val = compute_sum_numbers(n);
    
    proof {
        assert(sum_cubes_val as nat == sum_cubes(n as nat));
        assert(sum_numbers_val as nat == sum_numbers(n as nat));
        assert(sum_cubes(n as nat) >= sum_numbers(n as nat));
        assert(sum_cubes_val >= sum_numbers_val);
    }
    
    sum_cubes_val - sum_numbers_val
}

}