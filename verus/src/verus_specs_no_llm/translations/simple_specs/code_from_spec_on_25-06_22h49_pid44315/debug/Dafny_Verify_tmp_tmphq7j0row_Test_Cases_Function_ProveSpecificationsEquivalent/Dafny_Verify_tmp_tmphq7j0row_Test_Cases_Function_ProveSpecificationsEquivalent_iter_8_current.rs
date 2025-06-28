use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple_conditions(x: int) -> (r: int) 
    ensures r == 3 * x
{
    3 * x
}

// Method to demonstrate that the specification is satisfied
fn prove_specifications_equivalent(x: int) -> (r: int)
    ensures r == 3 * x
{
    let result = triple_conditions(x);
    assert(result == 3 * x);
    result
}

}