use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x+y,
        (m == x || m == y) && x <= m && y <= m
{
    let sum = x + y;
    let max = if x >= y { x } else { y };
    return (sum, max);
}

}

The implementation:
   - This ensures `m` is either `x` or `y` (satisfying `m == x || m == y`)
   - And that both `x <= m` and `y <= m` (m is the maximum)

The Verus verifier can automatically prove that this implementation satisfies all the postconditions.