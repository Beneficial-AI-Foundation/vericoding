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
    requires
        n >= 0
    ensures
        a == fact(n)
{
    let mut result: nat = 1;
    let mut i: nat = 1;
    
    while i <= n
        invariant
            result == fact(i - 1),
            i <= n + 1,
            i >= 1
        decreases n - i
    {
        result = result * i;
        i = i + 1;
    }
    
    result
}

}