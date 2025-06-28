use builtin::*;
use builtin_macros::*;

verus! {

spec fn Fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        Fib(n - 1) + Fib(n - 2)
    }
}

fn ComputeFib(n: nat) -> (x: nat)
    ensures
        x == Fib(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        // At this point we know n >= 2
        assert(n >= 2);
        
        let mut a: nat = 0;  // Fib(0)
        let mut b: nat = 1;  // Fib(1)
        let mut i: nat = 2;
        
        // Establish initial invariant
        assert(2 <= i <= n + 1);
        assert(a == Fib(0));
        assert(b == Fib(1));
        assert(a == Fib(i - 2));
        assert(b == Fib(i - 1));
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == Fib(i - 2),
                b == Fib(i - 1),
                n >= 2
        {
            // Store old values for proof
            let old_a = a;
            let old_b = b;
            let old_i = i;
            
            // Compute next Fibonacci number
            let temp = a + b;
            
            // Prove that temp equals Fib(i)
            assert(i >= 2);
            assert(temp == old_a + old_b);
            assert(old_a == Fib(old_i - 2));
            assert(old_b == Fib(old_i - 1));
            assert(temp == Fib(old_i - 2) + Fib(old_i - 1));
            
            // By definition of Fib for i >= 2
            assert(Fib(old_i) == Fib(old_i - 1) + Fib(old_i - 2));
            assert(temp == Fib(old_i));
            
            // Update variables
            a = b;
            b = temp;
            i = i + 1;
            
            // Prove invariant is maintained
            assert(2 <= i <= n + 1);  // i was incremented by 1
            assert(a == old_b);
            assert(old_b == Fib(old_i - 1));
            assert(old_i - 1 == (i - 1) - 1);
            assert(old_i - 1 == i - 2);
            assert(a == Fib(i - 2));
            
            assert(b == temp);
            assert(temp == Fib(old_i));
            assert(old_i == i - 1);
            assert(b == Fib(i - 1));
        }
        
        // When loop exits: i > n
        // From loop condition: i > n
        // From invariant: i <= n + 1
        // Therefore: i == n + 1
        assert(i > n);
        assert(i <= n + 1);  // from invariant
        assert(i == n + 1);
        
        // From invariant: b == Fib(i - 1)
        assert(b == Fib(i - 1));
        assert(i - 1 == n);
        assert(b == Fib(n));
        
        b
    }
}

fn main() {
}

}