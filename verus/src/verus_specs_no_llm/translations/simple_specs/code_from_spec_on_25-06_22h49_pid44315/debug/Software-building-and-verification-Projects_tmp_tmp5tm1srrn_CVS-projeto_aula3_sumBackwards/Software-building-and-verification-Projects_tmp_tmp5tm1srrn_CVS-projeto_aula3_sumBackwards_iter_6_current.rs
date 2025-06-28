use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}

fn sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    let mut result = 0;
    let mut i = n;
    
    while i > 0
        invariant
            result == sum(n) - sum(i),
            i <= n
        decreases i
    {
        // Before the update: result == sum(n) - sum(i)
        // We know that sum(i) == i + sum(i-1)
        assert(sum(i) == i + sum(i - 1));
        
        result = result + i;
        i = i - 1;
        
        // After the update: result_new == result_old + i_old
        //                                == sum(n) - sum(i_old) + i_old
        //                                == sum(n) - (i_old + sum(i_old - 1)) + i_old
        //                                == sum(n) - sum(i_old - 1)
        //                                == sum(n) - sum(i_new)
    }
    
    // At loop exit: i == 0, so sum(i) == sum(0) == 0
    // From invariant: result == sum(n) - sum(0) == sum(n) - 0 == sum(n)
    assert(i == 0);
    assert(sum(0) == 0);
    assert(result == sum(n) - sum(i));
    assert(result == sum(n));
    
    result
}

}