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
        
        while i <= n
            invariant 1 <= i <= n + 1
            invariant result == factorial(i - 1)
            invariant result >= 1
        {
            // Before the multiplication, result == factorial(i - 1)
            assert(result == factorial(i - 1));
            
            // After multiplication: result * i == factorial(i - 1) * i
            result = result * i;
            
            // We need to prove that factorial(i - 1) * i == factorial(i)
            // This follows from the definition of factorial when i > 0
            assert(i > 0);
            assert(factorial(i) == i * factorial(i - 1));
            assert(result == factorial(i));
            
            i = i + 1;
        }
        
        // When loop exits: i > n, and since i was <= n + 1, we have i == n + 1
        assert(i == n + 1);
        // From the invariant: result == factorial(i - 1) == factorial(n)
        assert(result == factorial(n));
        result
    }
}

}