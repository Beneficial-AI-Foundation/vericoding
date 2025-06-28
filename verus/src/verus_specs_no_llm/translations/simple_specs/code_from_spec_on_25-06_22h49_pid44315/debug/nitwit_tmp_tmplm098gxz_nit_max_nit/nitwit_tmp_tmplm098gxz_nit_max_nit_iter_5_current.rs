use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool 
    requires valid_base(b)
{
    n < b
}

spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn max_nit(b: nat) -> (nmax: nat)
    requires
        valid_base(b)
    ensures
        nitness(b, nmax),
        is_max_nit(b, nmax)
{
    let result = (b - 1) as nat;
    
    // Prove is_max_nit(b, result) 
    assert(result == b - 1);
    
    // Prove nitness(b, result)
    // We need to show that b - 1 < b, which is true when b >= 2
    assert(b >= 2);  // from precondition valid_base(b)
    
    // More explicit arithmetic proof
    assert(b - 1 < b) by {
        assert(b >= 1); // since b >= 2
        // For natural numbers, if b >= 1, then b - 1 < b
    };
    
    result
}

}