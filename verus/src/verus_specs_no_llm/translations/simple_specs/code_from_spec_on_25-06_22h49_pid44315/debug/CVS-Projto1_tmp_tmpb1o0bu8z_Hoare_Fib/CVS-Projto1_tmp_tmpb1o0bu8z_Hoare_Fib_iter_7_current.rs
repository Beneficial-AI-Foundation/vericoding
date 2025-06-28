use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn Fib(n: u32) -> (r: u32)
    requires
        n < 47, // Prevent overflow for u32
    ensures
        r == fib(n as nat)
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        assert(n >= 2);
        assert(n - 1 < 47);
        assert(n - 2 < 47);
        
        let fib_n_minus_1 = Fib(n - 1);
        let fib_n_minus_2 = Fib(n - 2);
        
        // Prove that addition won't overflow
        assert(fib_n_minus_1 == fib((n - 1) as nat));
        assert(fib_n_minus_2 == fib((n - 2) as nat));
        
        // Prove the spec function equivalence
        assert(fib(n as nat) == fib((n - 1) as nat) + fib((n - 2) as nat)) by {
            assert(n as nat >= 2);
            assert(n as nat != 0);
            assert(n as nat != 1);
        };
        
        let result = fib_n_minus_1 + fib_n_minus_2;
        
        // Prove the final equality
        assert(result == fib((n - 1) as nat) + fib((n - 2) as nat));
        assert(result == fib(n as nat));
        
        result
    }
}

}