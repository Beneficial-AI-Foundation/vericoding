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
        let mut a: u64 = 0;
        let mut b: u64 = 1;
        let mut i: u64 = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == fib((i - 2) as nat),
                b == fib((i - 1) as nat),
                n >= 2,
                i <= 50,
                n < 50,
            decreases n + 1 - i
        {
            let temp = a + b;
            
            // Proof assertions to help the verifier
            assert(temp == fib((i - 2) as nat) + fib((i - 1) as nat));
            assert(temp == fib(i as nat)) by {
                assert(fib(i as nat) == fib((i - 1) as nat) + fib((i - 2) as nat));
            };
            
            a = b;
            b = temp;
            i = i + 1;
        }
        
        assert(i == n + 1);
        assert(b == fib(n as nat));
        b
    }
}

fn main() {
}

}