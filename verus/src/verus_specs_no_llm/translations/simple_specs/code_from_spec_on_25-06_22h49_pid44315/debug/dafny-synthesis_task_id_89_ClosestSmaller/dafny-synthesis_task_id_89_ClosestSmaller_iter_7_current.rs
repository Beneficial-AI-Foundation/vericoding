use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn ClosestSmaller(n: int) -> int
    requires
        n > 0
    ensures
        |m: int| m + 1 == n
{
    n - 1
}

}