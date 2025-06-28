use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Par(n: int) -> bool {
    n % 2 == 0
}

fn FazAlgo(a: int, b: int) -> (x: int, y: int)
    requires
        a >= b && Par(a-b)
{
    // Since there are no postconditions, we can return any valid integers
    // Let's return values based on the inputs to make it more meaningful
    let diff = a - b;
    (diff / 2, a + b)
}

}