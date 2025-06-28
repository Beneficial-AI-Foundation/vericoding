use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HoareTripleReqEns(i: int, k: int) -> (result: int)
    // (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
    requires
        k == i*i
    ensures
        result == (i+1)*(i+1)
{
    let result = k + 2 * i + 1;
    
    // Prove the algebraic identity: (i+1)*(i+1) == i*i + 2*i + 1
    assert((i+1)*(i+1) == i*i + 2*i + 1) by (nonlinear_arith);
    
    // Use the precondition and algebraic substitution
    assert(result == k + 2*i + 1);
    assert(result == i*i + 2*i + 1) by {
        // k == i*i from precondition, so k + 2*i + 1 == i*i + 2*i + 1
        assert(k == i*i);
    };
    
    // Combine with the algebraic identity
    assert(result == (i+1)*(i+1)) by (nonlinear_arith);
    
    result
}

}