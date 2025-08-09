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
    // triple(x) = x * 2 + x = x * 3
    // So triple(x) / 3 = (x * 3) / 3 = x
    // And (triple(x) / 3) * 3 = x * 3 = triple(x)
    assert(triple(x) == x * 2 + x);
    assert(triple(x) == x * 3);
    assert(triple(x) / 3 == x);
    assert((triple(x) / 3) * 3 == triple(x));
}

}

fn main() {}