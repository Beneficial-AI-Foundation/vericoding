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

fn ComputeFib(n: nat) -> (x: nat)
    ensures
        x == Fib(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut a: nat = 0;
        let mut b: nat = 1;
        let mut i: nat = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                a == Fib(i - 2),
                b == Fib(i - 1),
        {
            let temp = a + b;
            proof {
                // Show that temp equals Fib(i)
                assert(temp == a + b);
                assert(a == Fib(i - 2));
                assert(b == Fib(i - 1));
                assert(temp == Fib(i - 2) + Fib(i - 1));
                // Use the definition of Fib for i >= 2
                assert(i >= 2);
                assert(Fib(i) == Fib(i - 1) + Fib(i - 2)) by {
                    // This follows from the definition of Fib since i >= 2
                };
                assert(temp == Fib(i));
            }
            a = b;
            b = temp;
            i = i + 1;
            proof {
                // Help verify the invariant after the updates
                assert(a == Fib((i - 1) - 1)) by {
                    assert(a == temp) by {
                        // a was assigned temp in the previous step
                    };
                    assert(temp == Fib(i - 1));
                    assert((i - 1) - 1 == i - 2);
                };
                assert(b == Fib(i - 1)) by {
                    assert(b == temp);
                    assert(temp == Fib((i - 1)));
                };
            }
        }
        
        proof {
            assert(i == n + 1);
            assert(b == Fib(i - 1));
            assert(i - 1 == n);
            assert(b == Fib(n));
        }
        b
    }
}

}