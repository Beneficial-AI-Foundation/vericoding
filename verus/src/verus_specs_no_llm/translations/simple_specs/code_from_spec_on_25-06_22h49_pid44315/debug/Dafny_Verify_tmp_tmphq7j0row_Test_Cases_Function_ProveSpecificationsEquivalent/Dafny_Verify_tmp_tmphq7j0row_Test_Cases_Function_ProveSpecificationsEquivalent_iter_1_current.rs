use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleConditions(x: int) -> (r: int) 
    ensures r == 3 * x
{
    3 * x
}

// Method to demonstrate that the specification is satisfied
fn ProveSpecificationsEquivalent(x: int) -> (r: int)
    ensures r == 3 * x
{
    TripleConditions(x)
}

}