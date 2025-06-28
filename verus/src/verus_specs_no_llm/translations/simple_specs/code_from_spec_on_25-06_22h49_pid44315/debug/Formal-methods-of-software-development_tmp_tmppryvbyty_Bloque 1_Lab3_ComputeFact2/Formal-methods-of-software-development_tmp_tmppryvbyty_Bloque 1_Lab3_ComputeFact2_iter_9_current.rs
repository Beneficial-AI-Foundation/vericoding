use builtin::*;
use builtin_macros::*;

verus! {

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// Helper lemma to establish bounds on factorial values
proof fn factorial_bounds(n: int)
    requires n >= 0 && n <= 12
    ensures factorial(n) <= 479001600  // 12! = 479,001,600 < u32::MAX
    decreases n
{
    if n <= 0 {
        assert(factorial(n) == 1);
    } else if n == 1 {
        assert(factorial(1) == 1);
    } else if n == 2 {
        factorial_bounds(1);
        assert(factorial(2) == 2 * factorial(1));
        assert(factorial(2) == 2);
    } else if n == 3 {
        factorial_bounds(2);
        assert(factorial(3) == 3 * factorial(2));
        assert(factorial(3) == 6);
    } else if n == 4 {
        factorial_bounds(3);
        assert(factorial(4) == 4 * factorial(3));
        assert(factorial(4) == 24);
    } else if n == 5 {
        factorial_bounds(4);
        assert(factorial(5) == 5 * factorial(4));
        assert(factorial(5) == 120);
    } else if n == 6 {
        factorial_bounds(5);
        assert(factorial(6) == 6 * factorial(5));
        assert(factorial(6) == 720);
    } else if n == 7 {
        factorial_bounds(6);
        assert(factorial(7) == 7 * factorial(6));
        assert(factorial(7) == 5040);
    } else if n == 8 {
        factorial_bounds(7);
        assert(factorial(8) == 8 * factorial(7));
        assert(factorial(8) == 40320);
    } else if n == 9 {
        factorial_bounds(8);
        assert(factorial(9) == 9 * factorial(8));
        assert(factorial(9) == 362880);
    } else if n == 10 {
        factorial_bounds(9);
        assert(factorial(10) == 10 * factorial(9));
        assert(factorial(10) == 3628800);
    } else if n == 11 {
        factorial_bounds(10);
        assert(factorial(11) == 11 * factorial(10));
        assert(factorial(11) == 39916800);
    } else if n == 12 {
        factorial_bounds(11);
        assert(factorial(12) == 12 * factorial(11));
        assert(factorial(12) == 479001600);
    }
}

// Helper lemma to prove factorial is monotonic for valid ranges
proof fn factorial_monotonic(n: int)
    requires n >= 0 && n <= 11
    ensures factorial(n) <= factorial(n + 1)
{
    assert(factorial(n + 1) == (n + 1) * factorial(n));
    assert(n + 1 >= 1);
    assert(factorial(n) >= 1) by {
        factorial_bounds(n);
    }
}

// Additional helper lemma for multiplication bounds
proof fn multiplication_bounds(n: u32, rec_result: u32)
    requires n <= 12 && rec_result == factorial((n - 1) as int) && n >= 1
    ensures (n as int) * (rec_result as int) == factorial(n as int)
    ensures factorial(n as int) <= 4294967295  // u32::MAX
{
    factorial_bounds(n as int);
    factorial_bounds((n - 1) as int);
    assert(factorial(n as int) == (n as int) * factorial((n - 1) as int));
    assert((rec_result as int) == factorial((n - 1) as int));
    assert((n as int) * (rec_result as int) == factorial(n as int));
    assert(factorial(n as int) <= 479001600);
    assert(479001600 <= 4294967295);
}

fn main() {
}

fn ComputeFact2(n: u32) -> (f: u32)
    requires
        n <= 12  // Ensure result fits in u32
    ensures
        f == factorial(n as int)
    decreases n
{
    if n == 0 {
        proof {
            assert(factorial(0) == 1);
        }
        1
    } else {
        let rec_result = ComputeFact2(n - 1);
        proof {
            // Use the helper lemma to establish bounds and correctness
            multiplication_bounds(n, rec_result);
            
            // Additional assertions to help Verus understand the overflow safety
            assert(rec_result as int == factorial((n - 1) as int));
            assert(factorial(n as int) <= 479001600);
            assert(n <= 12);
            assert(rec_result <= 479001600);
            
            // The key insight: since factorial(n) <= 479001600 < u32::MAX,
            // the multiplication won't overflow
            assert((n * rec_result) as int == (n as int) * (rec_result as int));
        }
        n * rec_result
    }
}

}