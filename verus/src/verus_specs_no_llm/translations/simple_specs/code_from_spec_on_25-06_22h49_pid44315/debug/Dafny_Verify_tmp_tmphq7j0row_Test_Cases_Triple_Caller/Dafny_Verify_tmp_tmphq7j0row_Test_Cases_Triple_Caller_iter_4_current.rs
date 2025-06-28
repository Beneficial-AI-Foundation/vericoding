use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleConditions(x: int) -> (r: int) 
    requires x % 2 == 0
    ensures r == 3 * x
{
    3 * x
}

fn Caller(x: int) -> (r: int)
    requires x % 2 == 0
    ensures r == 3 * x
{
    let result = TripleConditions(x);
    // The postcondition of TripleConditions guarantees result == 3 * x
    assert(result == 3 * x) by {
        // This follows directly from the ensures clause of TripleConditions
    };
    result
}

}