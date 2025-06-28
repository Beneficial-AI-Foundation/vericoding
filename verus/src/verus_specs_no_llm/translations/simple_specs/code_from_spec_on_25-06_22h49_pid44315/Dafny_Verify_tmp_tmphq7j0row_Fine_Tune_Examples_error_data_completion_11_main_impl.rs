use builtin::*;
use builtin_macros::*;

verus! {

fn main(x: int) -> (j: int, i: int)
    requires
        x > 0,
    ensures
        j == 2 * x,
        i == 0,
{
    (2 * x, 0)
}

}