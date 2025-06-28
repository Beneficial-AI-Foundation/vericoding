use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Triple(x: int) -> (r: int)
    ensures
        r == 3*x
{
    return 3 * x;
}

}

The implementation is straightforward:
- The function `Triple` takes an integer parameter `x`
- It returns `3 * x` which directly satisfies the postcondition `r == 3*x`
- I removed the duplicate `use builtin::*; use builtin_macros::*;` statements
- The function now correctly implements the specification by returning the triple of the input value

This implementation will verify successfully as it directly satisfies the ensures clause.