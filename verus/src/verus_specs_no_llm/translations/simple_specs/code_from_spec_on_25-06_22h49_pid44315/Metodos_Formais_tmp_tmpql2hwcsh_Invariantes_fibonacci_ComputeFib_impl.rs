use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

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

fn ComputeFib(n: u32) -> (x: u32)
    requires n < 100  // Add bound to prevent overflow
    ensures
        x == Fib(n as nat)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a: u32 = 0;
        let mut b: u32 = 1;
        let mut i: u32 = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == Fib((i - 2) as nat),
                b == Fib((i - 1) as nat),
                i <= 100,  // Maintain the bound
        {
            let temp = a + b;
            
            // Prove that temp equals Fib(i)
            assert(temp == a + b);
            assert(a == Fib((i - 2) as nat));
            assert(b == Fib((i - 1) as nat));
            assert(temp == Fib((i - 2) as nat) + Fib((i - 1) as nat));
            
            // Use the definition of Fib for i >= 2
            assert(i >= 2);
            assert(Fib(i as nat) == Fib((i - 1) as nat) + Fib((i - 2) as nat)) by {
                // Help Verus see that the definition applies
                assert(i as nat != 0);
                assert(i as nat != 1);
            }
            assert(temp == Fib(i as nat));
            
            a = b;
            b = temp;
            i = i + 1;
        }
        
        // After the loop, prove the postcondition
        assert(i == n + 1);
        assert(b == Fib((i - 1) as nat));
        assert((i - 1) as nat == n as nat);
        assert(b == Fib(n as nat));
        
        b
    }
}

}