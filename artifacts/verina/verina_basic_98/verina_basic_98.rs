use vstd::prelude::*;

verus! {

// Helper lemma for multiplication and division properties
proof fn mul_div_lemma(x: int)
    ensures 
        (x * 3) % 3 == 0,
        (x * 3) / 3 == x,
        ((x * 3) / 3) * 3 == x * 3
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x * 3, 3);
    assert((x * 3) % 3 == 0) by (nonlinear_arith);
    assert((x * 3) / 3 == x) by (nonlinear_arith);
    assert(((x * 3) / 3) * 3 == x * 3) by (nonlinear_arith);
}

spec fn triple_precond(x: int) -> bool {
    true
}

spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && (result / 3) * 3 == result
}

fn triple(x: i32) -> (result: i32)
    requires 
        triple_precond(x as int),
        -700000000 <= x <= 700000000
    ensures 
        triple_postcond(x as int, result as int)
{
    proof {
        mul_div_lemma(x as int);
    }
    x * 3
}

fn main() {
    let _result = triple(5);
}

} // verus!