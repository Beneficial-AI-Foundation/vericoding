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
        
        // At this point: result == fact(i-1) from the invariant
        // We know that fact(i) == i * fact(i-1) when i > 0
        
        assert(i > 0);
        assert(fact(i) == i * fact(i - 1));
        assert(result == fact(i - 1)); // From invariant before increment
        
        result = result * i;
        
        // Now result == fact(i-1) * i == i * fact(i-1) == fact(i)
        assert(result == fact(i - 1) * i);
        assert(fact(i - 1) * i == i * fact(i - 1));
        assert(i * fact(i - 1) == fact(i));
        assert(result == fact(i));
    }
    
    result
}

}