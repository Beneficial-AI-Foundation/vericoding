use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ClosestSmaller(n: int) -> (m: int)
    requires
        n > 0
    ensures
        m + 1 == n
{
    let result = n - 1;
    assert(result + 1 == n);
    result
}

}