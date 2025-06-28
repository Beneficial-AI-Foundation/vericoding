use builtin::*;
use builtin_macros::*;

verus! {

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

fn ComputeFib(n: u64) -> (f: u64)
    requires n < 50  // prevent overflow
    ensures f == fib(n as nat)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a: u64 = 0;  // fib(0)
        let mut b: u64 = 1;  // fib(1)
        let mut i: u64 = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat),
                n >= 2,
        {
            let temp = a + b;
            
            // Help the verifier understand that temp equals fib(i)
            assert(i >= 2);
            assert(fib(i as nat) == fib((i - 1) as nat) + fib((i - 2) as nat)) by {
                // The definition of fib for i >= 2 automatically gives us this
            };
            assert(temp == b + a);
            assert(temp == fib((i - 1) as nat) + fib((i - 2) as nat));
            assert(temp == fib(i as nat));
            
            a = b;
            b = temp;
            i = i + 1;
            
            // Help verify the invariant for the next iteration
            assert(a == fib((i - 2) as nat));
            assert(b == fib((i - 1) as nat));
        }
        
        // When loop exits, i == n + 1, so b == fib(n)
        assert(i == n + 1);
        assert(b == fib(((i - 1)) as nat));
        assert(b == fib(n as nat));
        b
    }
}

fn main() {
}

}