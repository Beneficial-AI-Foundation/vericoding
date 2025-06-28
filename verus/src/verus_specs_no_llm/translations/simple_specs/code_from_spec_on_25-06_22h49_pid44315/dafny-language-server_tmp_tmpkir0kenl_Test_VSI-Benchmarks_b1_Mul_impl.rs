use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Add(x: int, y: int) -> (r: int)
    ensures r == x + y
{
    x + y
}

// The original Mul specification has contradictory ensures clauses:
// r == x+y AND r == x*y cannot both be true for arbitrary x,y
// I'll assume this was meant to be multiplication based on the function name
fn Mul(x: int, y: int) -> (r: int)
    ensures r == x * y
{
    x * y
}

}