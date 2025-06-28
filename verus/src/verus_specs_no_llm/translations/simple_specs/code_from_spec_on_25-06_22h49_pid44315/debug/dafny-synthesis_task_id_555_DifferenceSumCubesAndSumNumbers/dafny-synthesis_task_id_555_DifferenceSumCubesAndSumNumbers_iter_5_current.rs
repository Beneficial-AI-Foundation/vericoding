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
        
        // Step by step algebraic manipulation
        calc! {
            (==)
            sum_numbers(n); {
                // By definition
            }
            n + sum_numbers(n - 1); {
                // By inductive hypothesis
            }
            n + ((n - 1) * n) / 2; {
                // Algebra: n = (2*n)/2
            }
            (2 * n) / 2 + ((n - 1) * n) / 2; {
                // Combine fractions
            }
            (2 * n + (n - 1) * n) / 2; {
                // Distribute
            }
            (2 * n + n * n - n) / 2; {
                // Simplify
            }
            (n + n * n) / 2; {
                // Factor
            }
            (n * (1 + n)) / 2; {
                // Rearrange
            }
            (n * (n + 1)) / 2;
        }
    }
}

// Lemma to prove the formula for sum of cubes using direct induction
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
        
        // By definition: sum_cubes(n) = n³ + sum_cubes(n-1)
        // By inductive hypothesis: sum_cubes(n-1) = ((n-1)² * n²) / 4
        
        calc! {
            (==)
            sum_cubes(n); {
                // By definition
            }
            n * n * n + sum_cubes(n - 1); {
                // By inductive hypothesis
            }
            n * n * n + ((n - 1) * (n - 1) * n * n) / 4; {
                // Factor out n²
            }
            n * n * n + (n * n * (n - 1) * (n - 1)) / 4; {
                // Factor n² from first term: n³ = (4*n³)/4
            }
            (4 * n * n * n) / 4 + (n * n * (n - 1) * (n - 1)) / 4; {
                // Combine fractions
            }
            (4 * n * n * n + n * n * (n - 1) * (n - 1)) / 4; {
                // Factor n²
            }
            (n * n * (4 * n + (n - 1) * (n - 1))) / 4; {
                // Expand (n-1)²
            }
            (n * n * (4 * n + n * n - 2 * n + 1)) / 4; {
                // Simplify
            }
            (n * n * (2 * n + n * n + 1)) / 4; {
                // Factor as (n+1)²
            }
            (n * n * (n + 1) * (n + 1)) / 4;
        }
    }
}

fn DifferenceSumCubesAndSumNumbers(n: int) -> (result: int)
    requires
        n >= 0
    ensures
        result == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
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