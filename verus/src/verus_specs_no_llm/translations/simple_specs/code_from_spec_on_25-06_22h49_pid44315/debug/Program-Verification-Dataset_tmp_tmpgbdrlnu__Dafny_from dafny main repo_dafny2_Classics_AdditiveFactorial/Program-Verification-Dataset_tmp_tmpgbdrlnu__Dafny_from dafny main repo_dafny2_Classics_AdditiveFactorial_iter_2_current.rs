use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

fn AdditiveFactorial(n: nat) -> (u: nat)
    ensures
        u == Factorial(n)
{
    if n == 0 {
        1
    } else {
        let mut result: nat = 1;
        let mut i: nat = 1;
        
        while i <= n
            invariant
                1 <= i <= n + 1,
                result == Factorial(i - 1)
        {
            result = result * i;
            i = i + 1;
        }
        
        result
    }
}

}