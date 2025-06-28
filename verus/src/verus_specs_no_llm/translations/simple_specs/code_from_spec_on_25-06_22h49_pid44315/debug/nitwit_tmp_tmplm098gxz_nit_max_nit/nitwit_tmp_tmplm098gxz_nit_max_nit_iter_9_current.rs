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
    // Since b >= 2, we know b > 0, so b - 1 is well-defined for nat
    let result = (b - 1) as nat;
    
    // The postconditions follow directly from the definitions and precondition
    proof {
        // is_max_nit(b, result) follows by definition since result == b - 1
        assert(is_max_nit(b, result));
        
        // nitness(b, result) follows since b - 1 < b when b >= 2
        assert(b >= 2);  // from precondition valid_base(b)
        assert(b - 1 < b);  // arithmetic fact
        assert(nitness(b, result));
    }
    
    result
}

}