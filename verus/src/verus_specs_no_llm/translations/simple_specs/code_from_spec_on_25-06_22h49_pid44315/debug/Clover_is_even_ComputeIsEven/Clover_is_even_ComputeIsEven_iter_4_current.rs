use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
    decreases x.abs()
{
    if x >= 0 {
        if x == 0 {
            true
        } else if x == 1 {
            false
        } else {
            assert(x >= 2);
            assert((x - 2).abs() < x.abs());
            let result = ComputeIsEven(x - 2);
            assert((x % 2 == 0) == ((x - 2) % 2 == 0)) by {
                // For any integer n, n ≡ (n-2) (mod 2)
                // This is because 2 ≡ 0 (mod 2)
                assert(x == (x - 2) + 2);
                assert(2 % 2 == 0);
                // By modular arithmetic: (a + b) % m = ((a % m) + (b % m)) % m
                // So x % 2 = ((x-2) % 2 + 2 % 2) % 2 = ((x-2) % 2 + 0) % 2 = (x-2) % 2
            };
            result
        }
    } else {
        assert(x < 0);
        assert((-x).abs() == x.abs());
        assert((-x) > 0);
        let result = ComputeIsEven(-x);
        assert((x % 2 == 0) == ((-x) % 2 == 0)) by {
            // For any integer n, n ≡ (-n) (mod 2)
            // This is because if n is even, -n is even; if n is odd, -n is odd
            // In modular arithmetic: (-n) % 2 = (-(n % 2)) % 2
            // Since n % 2 is either 0 or 1:
            // - If n % 2 = 0, then (-n) % 2 = (-0) % 2 = 0
            // - If n % 2 = 1, then (-n) % 2 = (-1) % 2 = 1 (since -1 ≡ 1 (mod 2))
            assert(x % 2 == 0 || x % 2 == 1);
            assert((-x) % 2 == 0 || (-x) % 2 == 1);
            if x % 2 == 0 {
                assert((-x) % 2 == 0);
            } else {
                assert(x % 2 == 1);
                assert((-x) % 2 == 1);
            }
        };
        result
    }
}

}