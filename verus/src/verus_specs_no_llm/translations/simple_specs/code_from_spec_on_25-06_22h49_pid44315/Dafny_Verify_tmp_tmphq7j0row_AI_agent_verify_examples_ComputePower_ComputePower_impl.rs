use builtin::*;
use builtin_macros::*;

verus! {

spec fn Power(n: int) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * Power(n - 1)
    }
}

fn main() {
}

fn ComputePower(N: int) -> (y: nat)
    requires
        N >= 0
    ensures
        y == Power(N)
{
    if N == 0 {
        return 1nat;
    }
    
    let mut result: nat = 1nat;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i)
        decreases N - i
    {
        proof {
            // We need to prove that after the updates, result * 2 == Power(i + 1)
            // This follows from the definition of Power and the current invariant
            assert(i + 1 > 0);
            assert(Power(i + 1) == 2nat * Power(i));
            assert(result == Power(i));
            assert(result * 2nat == 2nat * Power(i));
            assert(result * 2nat == Power(i + 1));
        }
        result = result * 2nat;
        i = i + 1;
    }
    
    proof {
        assert(i == N);
        assert(result == Power(i));
        assert(result == Power(N));
    }
    
    return result;
}

}