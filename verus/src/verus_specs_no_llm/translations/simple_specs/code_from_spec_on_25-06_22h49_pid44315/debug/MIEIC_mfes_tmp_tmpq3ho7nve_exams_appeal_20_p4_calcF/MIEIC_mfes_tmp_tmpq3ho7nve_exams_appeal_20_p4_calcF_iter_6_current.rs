use builtin::*;
use builtin_macros::*;

verus! {

// Specification function for Fibonacci sequence
spec fn F(n: nat) -> nat
    decreases n
{
    if n <= 1 {
        n
    } else {
        F(n - 1) + F(n - 2)
    }
}

fn main() {
}

fn calcF(n: nat) -> (res: nat)
    ensures
        res == F(n)
{
    if n <= 1 {
        return n;
    }
    
    let mut a: nat = 0;  // F(0)
    let mut b: nat = 1;  // F(1)
    let mut i: nat = 2;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            a == F(i - 2),
            b == F(i - 1),
        decreases n + 1 - i
    {
        let temp = a + b;
        proof {
            // Help Verus see that temp == F(i)
            assert(temp == a + b);
            assert(a == F(i - 2));
            assert(b == F(i - 1));
            assert(temp == F(i - 2) + F(i - 1));
            assert(i >= 2);
            // Since i >= 2, we have F(i) = F(i-1) + F(i-2)
            assert(F(i) == F(i - 1) + F(i - 2)) by {
                // The spec function definition gives us this directly
            };
            assert(temp == F(i));
        }
        a = b;
        proof {
            assert(a == F(i - 1));
        }
        b = temp;
        proof {
            assert(b == F(i));
            assert(i + 1 >= 2);
            assert(a == F(i - 1) == F((i + 1) - 2));
            assert(b == F(i) == F((i + 1) - 1));
        }
        i = i + 1;
    }
    
    proof {
        // After the loop, i == n + 1, so we computed F(n)
        assert(i == n + 1);
        assert(b == F(i - 1));
        assert(i - 1 == n);
        assert(b == F(n));
    }
    
    b
}

}