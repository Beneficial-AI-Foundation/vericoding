use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultiReturn(x: int, y: int) -> (more: int, less: int)
    requires
        y >= 0
    ensures
        less <= x <= more
{
    return (x + y, x - y);
}

}

This implementation works because:
- `more = x + y` and since `y >= 0`, we have `more >= x`
- `less = x - y` and since `y >= 0`, we have `less <= x`
- Therefore, `less <= x <= more` is satisfied

The constraint `y >= 0` from the precondition is essential to ensure both inequalities hold.