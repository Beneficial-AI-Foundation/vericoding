use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HoareTripleReqEns(i: int, k: int) -> (k': int)
	// (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
    requires
        k == i*i
    ensures
        k' == (i+1)*(i+1)
{
    let result = k + 2 * i + 1;
    
    // Prove the algebraic identity: (i+1)*(i+1) == i*i + 2*i + 1
    assert((i+1)*(i+1) == (i+1)*i + (i+1)*1) by (nonlinear_arith);
    assert((i+1)*i + (i+1)*1 == i*i + i + i + 1) by (nonlinear_arith);
    assert(i*i + i + i + 1 == i*i + 2*i + 1) by (nonlinear_arith);
    assert((i+1)*(i+1) == i*i + 2*i + 1) by (nonlinear_arith);
    
    // Since k == i*i (from precondition), we have:
    assert(result == k + 2*i + 1) by (nonlinear_arith);
    assert(result == i*i + 2*i + 1) by (nonlinear_arith);
    assert(result == (i+1)*(i+1)) by (nonlinear_arith);
    
    result
}

}