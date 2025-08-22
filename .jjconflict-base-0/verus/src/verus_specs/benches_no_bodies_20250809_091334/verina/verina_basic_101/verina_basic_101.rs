use vstd::prelude::*;

verus! {

// Precondition for Triple function
pub open spec fn triple_precond(x: int) -> bool {
    true
}

// Postcondition for Triple function
pub open spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && (result / 3) * 3 == result
}

// The Triple function implementation as a spec function
pub open spec fn triple(x: int) -> int
    recommends triple_precond(x)
{
    let y = x * 2;
    y + x
}

// Theorem that the function satisfies its specification
proof fn triple_spec_satisfied(x: int)
    requires triple_precond(x)
    ensures triple_postcond(x, triple(x))
{
    assume(false);  // TODO: Remove this line and implement the proof
}

}

fn main() {}