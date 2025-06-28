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
    
    // First establish the algebraic identity
    assert((i+1)*(i+1) == i*i + 2*i + 1) by (nonlinear_arith);
    
    // Now use the precondition k == i*i to show result == (i+1)*(i+1)
    assert(result == k + 2*i + 1);  // by definition
    assert(k == i*i);  // from precondition
    assert(result == i*i + 2*i + 1);  // substitution
    assert(result == (i+1)*(i+1)) by (nonlinear_arith);  // using the identity
    
    result
}

}