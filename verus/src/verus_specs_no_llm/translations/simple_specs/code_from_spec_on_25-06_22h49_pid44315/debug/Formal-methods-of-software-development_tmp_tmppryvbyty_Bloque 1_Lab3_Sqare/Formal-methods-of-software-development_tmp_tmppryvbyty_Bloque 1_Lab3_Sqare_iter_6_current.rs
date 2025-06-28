use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Square(a: int) -> int
    requires
        a >= 1,
    ensures
        Square(a) == a * a,
{
    a * a
}

}