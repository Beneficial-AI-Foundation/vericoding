use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for sum of numbers 1 to n
spec fn sum_numbers(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + sum_numbers(n - 1) }
}

// Spec function for sum of cubes 1^3 to n^3
spec fn sum_cubes(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n * n * n + sum_cubes(n - 1) }
}

// Lemma to prove the formula for sum of numbers
proof fn lemma_sum_numbers_formula(n: int)
    requires n >= 0
    ensures sum_numbers(n) == (n * (n + 1)) / 2
    decreases n
{
    if n == 0 {
        assert(sum_numbers(0) == 0);
        assert((0 * (0 + 1)) / 2 == 0);
    } else {
        lemma_sum_numbers_formula(n - 1);
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        assert(sum_numbers(n - 1) == ((n - 1) * n) / 2);
        assert(sum_numbers(n) == n + ((n - 1) * n) / 2);
        // Simplify step by step
        assert(n + ((n - 1) * n) / 2 == (2 * n + (n - 1) * n) / 2);
        assert((2 * n + (n - 1) * n) / 2 == (2 * n + n * n - n) / 2);
        assert((2 * n + n * n - n) / 2 == (n + n * n) / 2);
        assert((n + n * n) / 2 == (n * (1 + n)) / 2);
        assert((n * (1 + n)) / 2 == (n * (n + 1)) / 2);
    }
}

// Lemma to prove the formula for sum of cubes
proof fn lemma_sum_cubes_formula(n: int)
    requires n >= 0
    ensures sum_cubes(n) == (n * n * (n + 1) * (n + 1)) / 4
    decreases n
{
    if n == 0 {
        assert(sum_cubes(0) == 0);
        assert((0 * 0 * (0 + 1) * (0 + 1)) / 4 == 0);
    } else {
        lemma_sum_cubes_formula(n - 1);
        lemma_sum_numbers_formula(n);
        
        // We'll prove this using the mathematical identity that sum of cubes equals square of sum
        let sum_n = sum_numbers(n);
        
        assert(sum_n == (n * (n + 1)) / 2);
        
        // The key insight: we need to prove that sum_cubes(n) == sum_n * sum_n
        // This is a well-known mathematical identity, but we need to establish it inductively
        
        // Base case already handled above
        // For inductive step, we use the fact that:
        // sum_cubes(n) = n³ + sum_cubes(n-1)
        // and sum_numbers(n)² = (n + sum_numbers(n-1))²
        
        let sum_n_minus_1 = sum_numbers(n - 1);
        assert(sum_n_minus_1 == ((n - 1) * n) / 2);
        assert(sum_n == n + sum_n_minus_1);
        
        // From inductive hypothesis: sum_cubes(n-1) == sum_n_minus_1²
        assert(sum_cubes(n - 1) == (sum_n_minus_1 * sum_n_minus_1));
        
        // Now we need: n³ + sum_n_minus_1² == (n + sum_n_minus_1)²
        // Expanding: n³ + sum_n_minus_1² == n² + 2*n*sum_n_minus_1 + sum_n_minus_1²
        // So we need: n³ == n² + 2*n*sum_n_minus_1
        // Substituting sum_n_minus_1 = ((n-1)*n)/2:
        // n³ == n² + 2*n*((n-1)*n)/2 == n² + n*(n-1)*n == n² + n²*(n-1) == n² + n³ - n²== n³ ✓
        
        assert(n * n * n == n * n + 2 * n * sum_n_minus_1) by {
            assert(sum_n_minus_1 == ((n - 1) * n) / 2);
            assert(2 * n * sum_n_minus_1 == 2 * n * ((n - 1) * n) / 2);
            assert(2 * n * ((n - 1) * n) / 2 == n * (n - 1) * n);
            assert(n * (n - 1) * n == n * n * (n - 1));
            assert(n * n + n * n * (n - 1) == n * n * (1 + n - 1));
            assert(n * n * (1 + n - 1) == n * n * n);
        };
        
        // Now we can conclude
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        assert(sum_cubes(n) == n * n * n + sum_n_minus_1 * sum_n_minus_1);
        assert(sum_cubes(n) == n * n + 2 * n * sum_n_minus_1 + sum_n_minus_1 * sum_n_minus_1);
        assert(sum_cubes(n) == (n + sum_n_minus_1) * (n + sum_n_minus_1));
        assert(sum_cubes(n) == sum_n * sum_n);
        assert(sum_cubes(n) == ((n * (n + 1)) / 2) * ((n * (n + 1)) / 2));
        assert(sum_cubes(n) == (n * (n + 1) * n * (n + 1)) / 4);
        assert(sum_cubes(n) == (n * n * (n + 1) * (n + 1)) / 4);
    }
}

fn DifferenceSumCubesAndSumNumbers(n: int) -> int
    requires
        n >= 0
    ensures
        DifferenceSumCubesAndSumNumbers(n) == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    proof {
        lemma_sum_cubes_formula(n);
        lemma_sum_numbers_formula(n);
    }
    
    let sum_cubes_val = (n * n * (n + 1) * (n + 1)) / 4;
    let sum_numbers_val = (n * (n + 1)) / 2;
    
    sum_cubes_val - sum_numbers_val
}

}