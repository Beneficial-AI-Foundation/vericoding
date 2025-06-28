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
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == Fib(i - 2),
                b == Fib(i - 1),
                n >= 2
        {
            let temp = a + b;
            
            // Prove that temp equals Fib(i)
            assert(temp == a + b);
            assert(a == Fib(i - 2));
            assert(b == Fib(i - 1));
            assert(temp == Fib(i - 2) + Fib(i - 1));
            
            // Since i >= 2, by definition Fib(i) = Fib(i-1) + Fib(i-2)
            assert(i >= 2);
            assert(Fib(i) == Fib(i - 1) + Fib(i - 2));
            assert(temp == Fib(i));
            
            a = b;
            b = temp;
            i = i + 1;
        }
        
        // When loop exits: i > n, so i >= n + 1
        // From invariant: i <= n + 1, so i == n + 1
        assert(!(i <= n));
        assert(i >= n + 1);
        assert(i <= n + 1);  // from loop invariant
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