use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn plus_one(x: int) -> (r: int)
    requires
        x >= 0,
    ensures
        r == x + 1,
{
    x + 1
}

}