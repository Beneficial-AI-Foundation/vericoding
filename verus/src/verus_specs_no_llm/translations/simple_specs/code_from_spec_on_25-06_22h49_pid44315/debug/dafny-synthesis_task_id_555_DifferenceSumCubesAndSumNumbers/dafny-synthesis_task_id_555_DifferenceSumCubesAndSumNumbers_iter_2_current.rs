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
        assert(sum_numbers(n) == (2 * n + (n - 1) * n) / 2);
        assert(sum_numbers(n) == (2 * n + n * n - n) / 2);
        assert(sum_numbers(n) == (n + n * n) / 2);
        assert(sum_numbers(n) == (n * (1 + n)) / 2);
        assert(sum_numbers(n) == (n * (n + 1)) / 2);
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
        lemma_sum_numbers_formula(n - 1);
        
        // Use the identity: sum of cubes = (sum of numbers)^2
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        
        // The proof uses the mathematical identity that sum of first n cubes equals square of sum of first n numbers
        let sum_n = sum_numbers(n);
        let sum_n_minus_1 = sum_numbers(n - 1);
        
        assert(sum_n == (n * (n + 1)) / 2);
        assert(sum_n_minus_1 == ((n - 1) * n) / 2);
        
        // Using the identity: 1³ + 2³ + ... + n³ = (1 + 2 + ... + n)²
        assert(sum_cubes(n) == sum_n * sum_n);
        assert(sum_n * sum_n == ((n * (n + 1)) / 2) * ((n * (n + 1)) / 2));
        assert(sum_cubes(n) == (n * (n + 1) * n * (n + 1)) / 4);
        assert(sum_cubes(n) == (n * n * (n + 1) * (n + 1)) / 4);
    }
}

fn DifferenceSumCubesAndSumNumbers(n: int) -> (diff: int)
    requires
        n >= 0
    ensures
        diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    // Apply the lemmas to establish the formulas
    proof {
        lemma_sum_cubes_formula(n);
        lemma_sum_numbers_formula(n);
    }
    
    let sum_cubes = (n * n * (n + 1) * (n + 1)) / 4;
    let sum_numbers = (n * (n + 1)) / 2;
    
    // The postcondition should now verify with the lemmas
    sum_cubes - sum_numbers
}

}