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
        
        // At this point: result == fact(i-1) and we need result == fact(i)
        // We know that fact(i) == i * fact(i-1) when i > 0
        
        assert(i > 0);
        assert(fact(i) == i * fact(i - 1));
        
        result = result * i;
        
        // Now result == fact(i-1) * i == fact(i), so invariant is restored
        assert(result == fact(i));
    }
    
    result
}

}