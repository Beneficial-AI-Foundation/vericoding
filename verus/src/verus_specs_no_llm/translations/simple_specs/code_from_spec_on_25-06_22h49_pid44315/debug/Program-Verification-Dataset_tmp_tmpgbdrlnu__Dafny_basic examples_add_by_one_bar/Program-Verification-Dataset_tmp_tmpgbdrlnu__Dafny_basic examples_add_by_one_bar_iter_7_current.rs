use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn bar(x: int, y: int) -> (r: int)
    requires
        y >= 0
    ensures
        r == x + y
{
    x + y
}

}