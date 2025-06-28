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

// Helper lemma to establish bounds on Fibonacci values
proof fn fib_bounds(n: nat)
    ensures n < 47 ==> fib(n) <= 2971215073nat  // This is fib(46), which fits in u32
    decreases n
{
    if n < 47 {
        if n == 0 {
            assert(fib(0) == 0);
        } else if n == 1 {
            assert(fib(1) == 1);
        } else if n < 47 {
            fib_bounds(n - 1);
            fib_bounds(n - 2);
            assert(fib(n) == fib(n - 1) + fib(n - 2));
        }
    }
}

// Helper lemma for addition bounds
proof fn fib_addition_bound(n: nat)
    requires n >= 2 && n < 47
    ensures fib(n - 1) + fib(n - 2) <= u32::MAX
{
    fib_bounds(n - 1);
    fib_bounds(n - 2);
    assert(fib(n - 1) <= 2971215073nat);
    assert(fib(n - 2) <= 2971215073nat);
    assert(fib(n - 1) + fib(n - 2) <= 2971215073nat + 2971215073nat);
    assert(2971215073nat + 2971215073nat < u32::MAX);
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
        
        // Use the lemma to prove overflow safety
        fib_addition_bound(n as nat);
        assert(fib((n - 1) as nat) + fib((n - 2) as nat) <= u32::MAX);
        
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