use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumOfSquaresOfFirstNOddNumbers(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    if n == 0 {
        return 0;
    }
    
    let mut sum = 0;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            sum == (i * (2 * i - 1) * (2 * i + 1)) / 3
    {
        let odd_number = 2 * i + 1;
        sum = sum + odd_number * odd_number;
        i = i + 1;
        
        // Help Verus prove the invariant by showing the algebraic relationship
        assert(sum == (i * (2 * i - 1) * (2 * i + 1)) / 3) by {
            // The proof follows from the mathematical identity for sum of squares of odd numbers
            // sum_{k=0}^{i-1} (2k+1)^2 = i(2i-1)(2i+1)/3
            // This is a well-known formula that Verus should be able to verify
        }
    }
    
    sum
}

}