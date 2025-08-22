use vstd::prelude::*;

verus! {

spec fn triple_precond(x: int) -> bool {
    true
}

spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && result / 3 * 3 == result
}

fn triple(x: u32) -> (result: u32)
    requires 
        triple_precond(x as int),
        x <= u32::MAX / 3
    ensures 
        triple_postcond(x as int, result as int)
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}