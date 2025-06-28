use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int) -> (a: int, b: int)
    requires
        n >= 0
    ensures
        a + b == 3 * n
{
    return (3 * n, 0);
}

}

This implementation:
6. Sets `a = 3 * n` and `b = 0`, so `a + b = 3 * n + 0 = 3 * n`, satisfying the postcondition

The verification will succeed because the postcondition `a + b == 3 * n` is trivially satisfied when `a = 3 * n` and `b = 0`.