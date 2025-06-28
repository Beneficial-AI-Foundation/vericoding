use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_one(x: int, y: int) -> (r: int)
    requires
        y >= 0,
    ensures
        r == x + y,
{
    x + y
}

}

The implementation correctly satisfies the specification:
- It takes parameters `x: int` and `y: int`
- It requires `y >= 0` 
- It ensures the result `r == x + y`
- The implementation returns `x + y`, which directly satisfies the postcondition

The only formatting change I made was adding commas after the `requires` and `ensures` clauses, which is proper Verus syntax. This should now verify successfully.