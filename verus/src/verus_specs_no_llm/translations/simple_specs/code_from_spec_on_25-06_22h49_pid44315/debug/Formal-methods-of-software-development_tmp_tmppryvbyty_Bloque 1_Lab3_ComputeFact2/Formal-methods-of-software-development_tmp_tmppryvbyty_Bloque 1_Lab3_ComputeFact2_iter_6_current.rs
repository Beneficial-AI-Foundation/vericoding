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
        assert(factorial(2) == 2);
    } else if n == 3 {
        assert(factorial(3) == 6);
    } else if n == 4 {
        assert(factorial(4) == 24);
    } else if n == 5 {
        assert(factorial(5) == 120);
    } else if n == 6 {
        assert(factorial(6) == 720);
    } else if n == 7 {
        assert(factorial(7) == 5040);
    } else if n == 8 {
        assert(factorial(8) == 40320);
    } else if n == 9 {
        assert(factorial(9) == 362880);
    } else if n == 10 {
        assert(factorial(10) == 3628800);
    } else if n == 11 {
        assert(factorial(11) == 39916800);
    } else if n == 12 {
        assert(factorial(12) == 479001600);
    }
}

fn main() {
}

fn ComputeFact2(n: u32) -> (f: u32)
    requires
        n >= 0,
        n <= 12  // Ensure result fits in u32
    ensures
        f == factorial(n as int)
    decreases n
{
    if n == 0 {
        proof {
            assert(factorial(n as int) == factorial(0));
            assert(factorial(0) == 1);
        }
        1
    } else {
        let rec_result = ComputeFact2(n - 1);
        proof {
            assert(rec_result == factorial((n - 1) as int));
            assert(factorial(n as int) == (n as int) * factorial((n - 1) as int));
            assert(factorial(n as int) == (n as int) * (rec_result as int));
            
            // Prove bounds to ensure no overflow
            factorial_bounds(n as int);
            factorial_bounds((n - 1) as int);
            
            // Since n <= 12 and rec_result == factorial(n-1), we know the multiplication is safe
            assert(rec_result <= 479001600);
            assert(n <= 12);
            assert((n as int) * (rec_result as int) <= 479001600);
        }
        n * rec_result
    }
}

}