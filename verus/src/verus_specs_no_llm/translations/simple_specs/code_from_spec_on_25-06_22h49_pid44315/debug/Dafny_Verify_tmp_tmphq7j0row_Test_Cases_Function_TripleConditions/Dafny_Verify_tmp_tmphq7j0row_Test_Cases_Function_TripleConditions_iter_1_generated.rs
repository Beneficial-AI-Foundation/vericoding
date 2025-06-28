use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleConditions(x: int) -> (r: int)
    ensures
        r == 3 * x
{
    return 3 * x;
}

}

The implementation is straightforward:
- The function takes an integer parameter `x`
- It returns `3 * x` to satisfy the postcondition `r == 3 * x`
- The multiplication of integers is a basic arithmetic operation that Verus can verify automatically
- No additional proof steps are needed since the implementation directly matches the specification