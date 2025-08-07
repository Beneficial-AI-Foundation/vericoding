use vstd::prelude::*;

verus! {

spec fn multiple_returns_precond(x: int, y: int) -> bool {
    true
}

spec fn multiple_returns_postcond(x: int, y: int, result: (int, int)) -> bool {
    result.0 == x + y && result.1 + y == x
}

// Using mathematical integers to match the Lean version more closely
fn multiple_returns_spec(x: int, y: int) -> (r: (int, int))
    requires multiple_returns_precond(x, y)
    ensures multiple_returns_postcond(x, y, r)
{
    let more = x + y;
    let less = x - y;
    (more, less)
}

proof fn multiple_returns_spec_satisfied(x: int, y: int)
    requires multiple_returns_precond(x, y)
    ensures multiple_returns_postcond(x, y, (x + y, x - y))
{
    // The postcondition follows directly from the definition
    assert((x + y, x - y).0 == x + y);
    assert((x + y, x - y).1 + y == x - y + y);
    assert(x - y + y == x);
}

} // verus!

fn main() {}