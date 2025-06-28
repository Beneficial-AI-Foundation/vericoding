use builtin::*;
use builtin_macros::*;

verus! {

spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * fact(n - 1)
    }
}

fn main() {
}

fn factIter(n: nat) -> (a: nat)
    ensures
        a == fact(n)
{
    let mut result: nat = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            result == fact(i),
            0 <= i <= n
        decreases n - i
    {
        i = i + 1;
        result = result * i;
        
        // Proof to help Verus understand that result == fact(i) after the update
        assert(fact(i) == i * fact(i - 1)) by {
            // This follows from the definition of fact when i > 0
        };
        assert(result == fact(i)) by {
            // result was fact(i-1) before multiplication
            // result is now fact(i-1) * i == fact(i)
        };
    }
    
    result
}

}