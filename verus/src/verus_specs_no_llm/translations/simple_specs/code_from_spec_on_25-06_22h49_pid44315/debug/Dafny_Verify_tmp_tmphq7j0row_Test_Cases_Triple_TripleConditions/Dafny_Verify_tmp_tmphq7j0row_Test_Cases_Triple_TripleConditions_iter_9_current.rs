use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple_conditions(x: int) -> (r: int)
    requires
        x % 2 == 0
    ensures
        r == 3 * x
{
    3 * x
}

}