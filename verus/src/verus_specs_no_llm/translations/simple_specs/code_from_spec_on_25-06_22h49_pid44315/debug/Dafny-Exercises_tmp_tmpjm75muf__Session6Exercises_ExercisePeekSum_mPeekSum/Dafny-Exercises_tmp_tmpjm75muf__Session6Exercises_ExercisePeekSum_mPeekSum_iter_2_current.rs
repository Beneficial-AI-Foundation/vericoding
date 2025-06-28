use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn peekSum(v: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 || n > v.len() {
        0
    } else {
        v[n-1] + peekSum(v, (n-1) as nat)
    }
}

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len() > 0
    ensures
        sum == peekSum(v, v.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == peekSum(v, i)
    {
        sum = sum + v[i as int];
        i = i + 1;
        
        // Proof hint: after adding v[i-1], sum now equals peekSum(v, i)
        assert(sum == peekSum(v, i));
    }
    
    sum
}

}