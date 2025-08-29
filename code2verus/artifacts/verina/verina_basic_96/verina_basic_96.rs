use vstd::prelude::*;

verus! {

spec fn swap_simultaneous_precond(x: int, y: int) -> bool {
    true
}

fn swap_simultaneous(x: int, y: int) -> (result: (int, int))
    requires swap_simultaneous_precond(x, y)
    ensures result.0 == y && result.1 == x &&
            (x != y ==> result.0 != x && result.1 != y)
{
    (y, x)
}

}

fn main() {}