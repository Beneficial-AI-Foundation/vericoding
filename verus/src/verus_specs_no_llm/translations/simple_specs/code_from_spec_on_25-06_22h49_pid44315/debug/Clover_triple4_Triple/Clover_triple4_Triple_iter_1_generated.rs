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
- The ensures clause guarantees that the return value `r` equals `3*x`

This implementation will verify successfully as it directly computes and returns the required value that satisfies the specification.