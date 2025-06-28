use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn factImp(n: int) -> (r: int)
    requires n >= 0
    ensures r == factorial(n)
    ensures r >= 1
{
    if n <= 0 {
        1
    } else {
        let mut result = 1;
        let mut i = 1;
        
        // Establish initial invariant
        assert(result == 1);
        assert(factorial(0) == 1);
        assert(result == factorial(i - 1));
        
        while i <= n
            invariant 1 <= i <= n + 1
            invariant result == factorial(i - 1)
            invariant result >= 1
        {
            // Before update: result == factorial(i - 1)
            assert(factorial(i) == i * factorial(i - 1));
            result = result * i;
            // After update: result == factorial(i - 1) * i == factorial(i)
            assert(result == factorial(i));
            i = i + 1;
            // After i increment: result == factorial(i - 1) (for new i)
        }
        
        assert(i == n + 1);
        assert(result == factorial(n));
        result
    }
}

}