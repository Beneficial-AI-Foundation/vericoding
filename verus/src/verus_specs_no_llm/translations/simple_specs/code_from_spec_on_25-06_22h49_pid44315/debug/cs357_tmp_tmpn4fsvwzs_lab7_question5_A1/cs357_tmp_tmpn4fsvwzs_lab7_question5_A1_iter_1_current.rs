use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn A1(x: int, y: int) -> (r: int)
    ensures
        r == x + y
{
    return x + y;
}

}